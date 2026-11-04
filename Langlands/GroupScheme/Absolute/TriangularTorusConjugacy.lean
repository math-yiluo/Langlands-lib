import Langlands.GroupScheme.Absolute.TriangularSplitExtension
import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectOfSection
import Langlands.GroupScheme.Absolute.SolvableTriangularEmbeddingProof
import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.Rational.TorusQuotientMaximalConjugacy
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Conjugacy of triangular homomorphisms from a split torus

Over an algebraically closed field, two natural families of upper triangular homomorphisms from
the points of a split torus that agree modulo unitriangular matrices are conjugate, by an element
of any subgroup of `GL_N(k)` that contains their quotients at the rational points and is
normalized by one of them. The proof is the layer-by-layer averaging of
`Absolute/TriangularTorusLift`, with each correction chosen inside that subgroup. For group
schemes with a closed upper triangular embedding this gives conjugacy of homomorphisms from a
split torus that agree modulo a unipotent normal subgroup, and hence the conjugacy of maximal
tori in smooth connected solvable groups over algebraically closed fields.
-/

noncomputable section

universe u

open Matrix
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TriangularLayer

variable {k : Type u} [Field k] {I : Type u} {N : ℕ}

/-- The approximation relation modulo the trivial subgroup is membership in the filtration. -/
theorem approx_bot_iff {A : Type*} [CommRing A] {a : ℕ} {g : GL (Fin N) A} :
    Approx (⊥ : Subgroup (GL (Fin N) A)) a g ↔ g ∈ W A N a := by
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    rw [Subgroup.mem_bot.1 hu, one_mul]
    exact hw
  · exact approx_of_mem_W

/-- The constant Laurent coefficients commute with taking a layer. -/
theorem layer_map_coeff [Fintype I] {a : ℕ} (C : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))) :
    (layer (AddMonoidAlgebra k (I → ℤ)) N a C).map (fun f => f.coeff 0) =
      layer k N a (C.map fun f => f.coeff 0) := by
  ext i j
  simp only [Matrix.map_apply, layer_apply]
  split_ifs <;> simp

namespace TorusLift

variable (k I N) in
/-- A natural family of upper triangular homomorphisms, as a lift with trivial kernel. -/
def ofHom (S : ∀ (A : Type u) [CommRing A] [Algebra k A], (I → Aˣ) →* GL (Fin N) A)
    (hnat : ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
      (φ : A →ₐ[k] B) (t : I → Aˣ),
      Matrix.GeneralLinearGroup.map (φ : A →+* B) (S A t) =
        S B (fun i => Units.map φ.toMonoidHom (t i)))
    (hup : ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ), S A t ∈ upper A N) :
    TorusLift k I N where
  lift A _ _ t := S A t
  kernel _ _ _ := ⊥
  lift_naturality := hnat
  map_mem_kernel A B _ _ _ _ φ x hx := by
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, map_one]
  lift_mem_upper := hup
  kernel_le _ _ _ := bot_le
  lift_mul_mem A _ _ t t' := by
    rw [Subgroup.mem_bot, map_mul, inv_mul_cancel]
  conj_mem A _ _ t x hx := by
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, mul_one, inv_mul_cancel]

variable (𝓛 : TorusLift k I N)

theorem correction_mul_right {A : Type u} [CommRing A] [Algebra k A] (x v : GL (Fin N) k)
    (t : I → Aˣ) :
    𝓛.correction (x * v) t = (Matrix.GeneralLinearGroup.map (algebraMap k A) v)⁻¹ *
      𝓛.correction x t * Matrix.GeneralLinearGroup.map (algebraMap k A) v := by
  simp only [correction, map_mul]
  group

/-- One step of the induction along the superdiagonal filtration, for a correction by any
matrix of the `a`-th filtration term with the prescribed layer. -/
theorem approx_succ_of_layer [Fintype I] [DecidableEq I] [IsAlgClosed k] {x : GL (Fin N) k}
    (hx : x ∈ W k N 0) {a : ℕ} {C : Matrix (Fin N) (Fin N) (AddMonoidAlgebra k (I → ℤ))}
    (hC : Rel (𝓛.kernel _) a (𝓛.deviation x (laurentVar I k)) C)
    (h : ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ),
      Approx (𝓛.kernel A) a (𝓛.deviation x t))
    {z : GL (Fin N) k} (hz : z ∈ W k N a)
    (hzl : layer k N a ((z : Matrix (Fin N) (Fin N) k) - 1) =
      layer k N a (C.map fun f => f.coeff 0))
    (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ) :
    Approx (𝓛.kernel A) (a + 1) (𝓛.deviation (x * z) t) := by
  obtain ⟨V, hV⟩ := (h A t).rel
  have key := 𝓛.layer_coeff_mem hC hV
  rw [layer_map] at key
  have hzA : Matrix.GeneralLinearGroup.map (algebraMap k A) z ∈ W A N a := map_mem_W hz _
  have hc : 𝓛.correction x t ∈ upper A N := 𝓛.correction_mem_upper hx t
  have e : 𝓛.deviation (x * z) t = (Matrix.GeneralLinearGroup.map (algebraMap k A) z)⁻¹ *
      ((𝓛.correction x t)⁻¹ * Matrix.GeneralLinearGroup.map (algebraMap k A) z *
        𝓛.correction x t * 𝓛.deviation x t) := by
    simp only [deviation, correction, map_mul]
    group
  rw [e]
  have hr := Rel.mul (𝓛.kernel_le A) (rel_of_mem_W ((W A N a).inv_mem hzA))
    (Rel.mul (𝓛.kernel_le A) (rel_of_mem_W (W_conj hc hzA)) hV)
  apply hr.approx_succ
  rw [map_add, map_add, layer_inv hzA, layer_conj hc hzA, layer_map_W, hzl,
    scale_correction 𝓛 hx]
  have := (layerGroup (𝓛.kernel A) a).neg_mem key
  convert this using 1
  abel

end TorusLift

section Conjugacy

variable [Fintype I] [DecidableEq I] [IsAlgClosed k]

/-- **Conjugacy of triangular homomorphisms.** Over an algebraically closed field, two natural
families of upper triangular homomorphisms from the points of a split torus which agree modulo
unitriangular matrices are conjugate by an element of any subgroup of `GL_N(k)` containing their
quotients at the rational points and normalized by the second family at the rational points. -/
theorem exists_conj_of_hom
    (S P : ∀ (A : Type u) [CommRing A] [Algebra k A], (I → Aˣ) →* GL (Fin N) A)
    (hSn : ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
      (φ : A →ₐ[k] B) (t : I → Aˣ),
      Matrix.GeneralLinearGroup.map (φ : A →+* B) (S A t) =
        S B (fun i => Units.map φ.toMonoidHom (t i)))
    (hPn : ∀ (A B : Type u) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
      (φ : A →ₐ[k] B) (t : I → Aˣ),
      Matrix.GeneralLinearGroup.map (φ : A →+* B) (P A t) =
        P B (fun i => Units.map φ.toMonoidHom (t i)))
    (hPu : ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ), P A t ∈ upper A N)
    (hPS : ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ), (P A t)⁻¹ * S A t ∈ W A N 0)
    (𝒱 : Subgroup (GL (Fin N) k)) (hPS𝒱 : ∀ t : I → kˣ, (P k t)⁻¹ * S k t ∈ 𝒱)
    (hP𝒱 : ∀ t : I → kˣ, ∀ v ∈ 𝒱, (P k t)⁻¹ * v * P k t ∈ 𝒱) :
    ∃ v ∈ 𝒱, ∀ (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ),
      S A t = (Matrix.GeneralLinearGroup.map (algebraMap k A) v)⁻¹ * P A t *
        Matrix.GeneralLinearGroup.map (algebraMap k A) v := by
  have hSu (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ) : S A t ∈ upper A N := by
    have e : S A t = P A t * ((P A t)⁻¹ * S A t) := by group
    rw [e]
    exact (upper A N).mul_mem (hPu A t) (W_le_upper 0 (hPS A t))
  let 𝓢 := TorusLift.ofHom k I N S hSn hSu
  let 𝓟 := TorusLift.ofHom k I N P hPn hPu
  obtain ⟨y, hy, hyP⟩ := 𝓟.exists_deviation_mem
  -- The corrections of both families by `y` are the second family.
  have hcorr (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ) :
      𝓢.correction y t = P A t := by
    have hP : 𝓟.correction y t = P A t := by
      have := Subgroup.mem_bot.1 (hyP A t)
      rw [TorusLift.deviation, inv_mul_eq_one] at this
      exact this
    rw [← hP]
    have hd : 𝓢.diagLift t = 𝓟.diagLift t := by
      have e : (⟨S A t, hSu A t⟩ : upper A N) =
          ⟨P A t, hPu A t⟩ * ⟨_, W_le_upper 0 (hPS A t)⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        group
      change diagPart A N ⟨S A t, hSu A t⟩ = diagPart A N ⟨P A t, hPu A t⟩
      rw [e, map_mul, diagPart_eq_one (g := ⟨_, W_le_upper 0 (hPS A t)⟩) (hPS A t), mul_one]
    simp only [TorusLift.correction, hd]
  -- The deviation after a further correction by `v`.
  have hdev (v : GL (Fin N) k) (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ) :
      𝓢.deviation (y * v) t = ((Matrix.GeneralLinearGroup.map (algebraMap k A) v)⁻¹ * P A t *
        Matrix.GeneralLinearGroup.map (algebraMap k A) v)⁻¹ * S A t := by
    rw [TorusLift.deviation, TorusLift.correction_mul_right, hcorr]
    rfl
  -- At the rational points, the deviation lies in `𝒱`.
  have hk (v : GL (Fin N) k) (hv : v ∈ 𝒱) (t : I → kˣ) : 𝓢.deviation (y * v) t ∈ 𝒱 := by
    rw [hdev, Algebra.algebraMap_self, Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply]
    have e : (v⁻¹ * P k t * v)⁻¹ * S k t = v⁻¹ * ((P k t)⁻¹ * v * P k t) * ((P k t)⁻¹ * S k t) := by
      group
    rw [e]
    exact 𝒱.mul_mem (𝒱.mul_mem (𝒱.inv_mem hv) (hP𝒱 t v hv)) (hPS𝒱 t)
  have key (a : ℕ) : ∃ v ∈ 𝒱, v ∈ W k N 0 ∧ ∀ (A : Type u) [CommRing A] [Algebra k A]
      (t : I → Aˣ), 𝓢.deviation (y * v) t ∈ W A N a := by
    induction a with
    | zero =>
        refine ⟨1, 𝒱.one_mem, (W k N 0).one_mem, fun A _ _ t => ?_⟩
        rw [hdev, map_one, inv_one, one_mul, mul_one]
        exact hPS A t
    | succ a ih =>
        obtain ⟨v, hv𝒱, hv, h⟩ := ih
        let R := AddMonoidAlgebra k (I → ℤ)
        let C : Matrix (Fin N) (Fin N) R :=
          ((𝓢.deviation (y * v) (laurentVar I k) : GL (Fin N) R) : Matrix (Fin N) (Fin N) R) - 1
        have hC : Rel (𝓢.kernel R) a (𝓢.deviation (y * v) (laurentVar I k)) C :=
          rel_of_mem_W (h R _)
        have hM : (layer R N a C).map (fun f => f.coeff 0) ∈ layerGroup 𝒱 a := by
          apply splitTorus.map_coeff_zero_mem k I (layerGroup 𝒱 a) (layer R N a C)
          intro φ
          have e : (layer R N a C).map φ = layer k N a (((Matrix.GeneralLinearGroup.map
              (φ : R →+* k) (𝓢.deviation (y * v) (laurentVar I k)) : GL (Fin N) k) :
                Matrix (Fin N) (Fin N) k) - 1) :=
            (layer_map_W a _ (φ : R →+* k)).symm
          rw [e, TorusLift.deviation_naturality]
          exact ⟨_, hk v hv𝒱 _, h k _, rfl⟩
        rw [layer_map_coeff] at hM
        obtain ⟨z, hz𝒱, hz, hzl⟩ := hM
        refine ⟨v * z, 𝒱.mul_mem hv𝒱 hz𝒱, (W k N 0).mul_mem hv (W_anti (Nat.zero_le a) hz),
          fun A _ _ t => ?_⟩
        rw [← mul_assoc, ← approx_bot_iff]
        exact 𝓢.approx_succ_of_layer ((W k N 0).mul_mem hy hv) hC
          (fun A _ _ t => approx_bot_iff.2 (h A t)) hz hzl A t
  obtain ⟨v, hv𝒱, -, h⟩ := key N
  refine ⟨v, hv𝒱, fun A _ _ t => ?_⟩
  have h1 := eq_one_of_mem_W_top (h A t)
  rw [hdev, inv_mul_eq_one] at h1
  exact h1.symm

end Conjugacy

/-! ### Conjugacy of homomorphisms from a split torus into a triangular group scheme -/

section Scheme

open PointedCoordinateWeights

/-- The structure morphism of the spectrum of the field itself is the identity. -/
theorem specOf_self_hom : (specOf (k := k) k).hom = 𝟙 (Spec (CommRingCat.of k)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

/-- The spectrum of the field is terminal over the base. -/
theorem specOf_self_hom_ext {X : Over (Spec (CommRingCat.of k))} (f g : X ⟶ specOf (k := k) k) :
    f = g := by
  apply Over.OverMorphism.ext
  have hf := Over.w f
  have hg := Over.w g
  rw [specOf_self_hom] at hf hg
  erw [Category.comp_id] at hf hg
  rw [hf, hg]

/-- The spectrum of the field as a test scheme over the base. -/
def baseTest : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ specOf (k := k) k :=
  Over.homMk (𝟙 _) (by erw [Category.id_comp, specOf_self_hom]; rfl)

/-- A rational point, viewed as a point over the base, pulled back to an affine test scheme. -/
theorem constantPoint_baseTest {H : GroupScheme (Spec (CommRingCat.of k))} {A : Type u}
    [CommRing A] [Algebra k A] (g : Lie.AffinePoints H k) :
    H.constantPoint (baseTest ≫ g) (specOf A) = Lie.affineMap H (Algebra.ofId k A) g := by
  rw [constantPoint, Lie.affineMap_apply, ← Category.assoc]
  congr 1

variable (I) [Fintype I] {H U : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ H)
  (j : H ⟶ upperScheme k N)

local notation "𝔻" => splitTorus (Spec (CommRingCat.of k)) I

/-- The matrices of the images of the torus points under a homomorphism. -/
def pointMatrix (ρ : 𝔻 ⟶ H) (A : Type u) [CommRing A] [Algebra k A] :
    (I → Aˣ) →* GL (Fin N) A :=
  MonoidHom.mk' (fun t => matrixOf j A (torusPoint I A t ≫ ρ.hom.hom)) fun t t' => by
    change matrixOf j A ((splitTorus.algebraPointsEquiv I A).symm (t * t') ≫ ρ.hom.hom) = _
    rw [map_mul, MonObj.mul_comp, map_mul]

theorem pointMatrix_apply (ρ : 𝔻 ⟶ H) {A : Type u} [CommRing A] [Algebra k A] (t : I → Aˣ) :
    pointMatrix I j ρ A t = matrixOf j A (torusPoint I A t ≫ ρ.hom.hom) :=
  rfl

theorem pointMatrix_naturality (ρ : 𝔻 ⟶ H) (A B : Type u) [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] (φ : A →ₐ[k] B) (t : I → Aˣ) :
    Matrix.GeneralLinearGroup.map (φ : A →+* B) (pointMatrix I j ρ A t) =
      pointMatrix I j ρ B (fun i => Units.map φ.toMonoidHom (t i)) := by
  rw [pointMatrix_apply, pointMatrix_apply, ← torusPoint_naturality, ← matrixOf_naturality,
    Lie.affineMap_apply, Lie.affineMap_apply, Category.assoc]

theorem pointMatrix_mem_upper (ρ : 𝔻 ⟶ H) (A : Type u) [CommRing A] [Algebra k A]
    (t : I → Aˣ) : pointMatrix I j ρ A t ∈ upper A N :=
  upperMatrix_mem_upper _

variable {I}

/-- The matrices of the points of a unipotent subgroup are unitriangular. -/
theorem matrixOf_mem_W_of_mem_range (hU : IsUnipotent U) {A : Type u} [CommRing A]
    [Algebra k A] {h : Lie.AffinePoints H A}
    (hh : h ∈ (SubgroupFunctor.range i).carrier (specOf A)) : matrixOf j A h ∈ W A N 0 := by
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hh
  apply upperMatrix_mem_W
  have h1 := hU.comp_eq_one_of_isSplitTorus isSplitTorus_blockLeviScheme
    (i ≫ j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) _) (specOf A) y
  simpa only [Grp.comp_hom_hom, Category.assoc] using h1

attribute [local instance] isAffineHom_splitTorus_spec

variable (I) [DecidableEq I] [IsAlgClosed k]

/-- **Conjugacy of triangular homomorphisms from a split torus.** Over an algebraically closed
field, two homomorphisms from a split torus into a group scheme with a closed upper triangular
embedding, whose quotient at every point lies in a unipotent normal subgroup, are conjugate by
an inner automorphism. -/
theorem exists_innerIso_of_triangular [Mono j.hom.hom] (hU : IsUnipotent U)
    (hn : (SubgroupFunctor.range i).IsNormal) (ρ ρ' : 𝔻 ⟶ H)
    (hρ : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ (𝔻).X),
      (x ≫ ρ.hom.hom)⁻¹ * (x ≫ ρ'.hom.hom) ∈ (SubgroupFunctor.range i).carrier T) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X, ρ ≫ (H.innerIso g).hom = ρ' := by
  have hquot (A : Type u) [CommRing A] [Algebra k A] (t : I → Aˣ) :
      (pointMatrix I j ρ A t)⁻¹ * pointMatrix I j ρ' A t =
        matrixOf j A ((torusPoint I A t ≫ ρ.hom.hom)⁻¹ * (torusPoint I A t ≫ ρ'.hom.hom)) := by
    rw [map_mul, map_inv]
    rfl
  obtain ⟨v, hv, hS⟩ := exists_conj_of_hom (pointMatrix I j ρ') (pointMatrix I j ρ)
    (pointMatrix_naturality I j ρ') (pointMatrix_naturality I j ρ) (pointMatrix_mem_upper I j ρ)
    (fun A _ _ t => by rw [hquot]; exact matrixOf_mem_W_of_mem_range i j hU (hρ _ _))
    (((SubgroupFunctor.range i).carrier (specOf k)).map (matrixOf j k))
    (fun t => Subgroup.mem_map.2 ⟨_, hρ _ (torusPoint I k t), (hquot k t).symm⟩)
    (fun t v hv => by
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hv
      refine Subgroup.mem_map.2 ⟨(torusPoint I k t ≫ ρ.hom.hom)⁻¹ * h *
        (torusPoint I k t ≫ ρ.hom.hom), ?_, by rw [map_mul, map_mul, map_inv]; rfl⟩
      have h1 := hn _ (torusPoint I k t ≫ ρ.hom.hom)⁻¹ h (Subgroup.mem_top _) hh
      rwa [inv_inv] at h1)
  obtain ⟨g₀, -, rfl⟩ := Subgroup.mem_map.1 hv
  refine ⟨baseTest ≫ g₀⁻¹, ?_⟩
  apply Grp.hom_ext
  apply affine_hom_ext
  intro A _ _ x
  obtain ⟨t, rfl⟩ : ∃ t, torusPoint I A t = x :=
    ⟨_, (splitTorus.algebraPointsEquiv I A).symm_apply_apply x⟩
  apply matrixOf_injective j
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, map_mul, map_mul, map_inv,
    constantPoint_baseTest, matrixOf_naturality, map_inv, map_inv, inv_inv]
  exact (hS A t).symm

end Scheme

end Langlands.GroupScheme.TriangularLayer

namespace Langlands.GroupScheme

/-! ### Conjugacy of maximal tori in solvable groups from the torus quotient

Let `H` be a smooth connected solvable affine group over an algebraically closed field, with a
homomorphism `q : H ⟶ D` onto a split torus whose scheme kernel has the points of a unipotent
normal subgroup `i : U ⟶ H`. Two homomorphisms from a torus to `H` with the same composite
with `q` are conjugate by a rational point of `H`. If `q` has a homomorphic section, then every
maximal torus of `H` maps isomorphically onto `D`, and any two maximal tori of `H` are
conjugate. Combined with the existence of the quotient and of the section, this gives the
conjugacy of maximal tori in smooth connected solvable groups over algebraically closed fields
(compare Milne 2017, Theorem 16.27(b)) and Milne 2017, Theorem 16.33(d).
-/

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H U D : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left]
  {i : U ⟶ H} {q : H ⟶ D}

/-- Two homomorphisms from a torus into a smooth connected solvable group over an algebraically
closed field that agree modulo a unipotent normal subgroup, the points of the scheme kernel of
`q`, are conjugate by a rational point. -/
theorem subgroupConjugate_of_comp_eq_of_isUnipotent (hH : IsSolvableGroupScheme H)
    (hU : IsUnipotent U) (hn : (SubgroupFunctor.range i).IsNormal)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T.toGrp)
    (s s' : T.toGrp ⟶ H) (h : s ≫ q = s' ≫ q) : SubgroupConjugate s s' := by
  classical
  obtain ⟨N, j, hj⟩ := solvableTriangularEmbeddingStatement k H hH
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  obtain ⟨I, hI, ⟨f⟩⟩ :=
    IsTorus.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting hT
  have : Fintype I := Fintype.ofFinite I
  have hρ : (f.inv ≫ s) ≫ q = (f.inv ≫ s') ≫ q := by
    rw [Category.assoc, h, Category.assoc]
  obtain ⟨g, hg⟩ := TriangularLayer.exists_innerIso_of_triangular I i j hU hn
    (f.inv ≫ s) (f.inv ≫ s') (fun V x => by
      rw [← hq, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp, inv_mul_eq_one,
        Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hρ])
  refine ⟨g, Iso.refl _, ?_⟩
  rw [Iso.refl_hom, Category.id_comp]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using f.hom ≫= hg

/-- Under the hypotheses of `subgroupConjugate_of_comp_eq_of_isUnipotent`, if `D` is a split
torus and `q` has a homomorphic section, then every maximal torus `s` of `H` maps
isomorphically onto `D` by `q`. -/
theorem isIso_comp_of_section_of_isUnipotent (hH : IsSolvableGroupScheme H)
    (hU : IsUnipotent U) (hn : (SubgroupFunctor.range i).IsNormal)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i) (hD : IsSplitTorus D)
    (σ : D ⟶ H) (hσ : σ ≫ q = 𝟙 D)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (s : T.toGrp ⟶ H) (hs : IsMaximalTorus s) :
    IsIso (s ≫ q) :=
  hs.isIso_comp_of_torus_section q σ hσ hD.isTorus
    (subgroupConjugate_of_comp_eq_of_isUnipotent hH hU hn hq hs.1 s)

/-- Under the hypotheses of `isIso_comp_of_section_of_isUnipotent`, any two maximal tori of
`H` are conjugate by a rational point. -/
theorem maximalToriAreConjugate_of_section_of_isUnipotent (hH : IsSolvableGroupScheme H)
    (hU : IsUnipotent U) (hn : (SubgroupFunctor.range i).IsNormal)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i) (hD : IsSplitTorus D)
    (σ : D ⟶ H) (hσ : σ ≫ q = 𝟙 D) : MaximalToriAreConjugate H := by
  intro T T' s s' hs hs'
  have := isIso_comp_of_section_of_isUnipotent hH hU hn hq hD σ hσ s hs
  have := isIso_comp_of_section_of_isUnipotent hH hU hn hq hD σ hσ s' hs'
  obtain ⟨g, e, he⟩ := subgroupConjugate_of_comp_eq_of_isUnipotent hH hU hn hq hs.1 s
    ((s ≫ q) ≫ inv (s' ≫ q) ≫ s')
    (by simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id])
  refine ⟨g, e ≪≫ asIso (s ≫ q) ≪≫ (asIso (s' ≫ q)).symm, ?_⟩
  rw [he]
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]

/-- **Conjugacy of maximal tori in solvable groups over algebraically closed fields** (compare
Milne 2017, Theorem 16.27(b)), from the existence of the split torus quotient with unipotent
kernel (Theorem 16.33(a), (c)) and of a homomorphic section of it (Theorem 16.26(a)). -/
theorem maximalToriAreConjugate_of_solvableTorusQuotient
    (hquot : SolvableTorusQuotientStatement.{u}) (hsec : SolvableSplitExtensionStatement.{u}) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (B : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left],
      IsSolvableGroupScheme B → MaximalToriAreConjugate B := by
  intro k _ _ H _ _ _ hH
  obtain ⟨U, D, i, q, hi, hUs, hUc, hU, hn, hfppf, hD⟩ := hquot k H hH
  obtain ⟨σ, hσ⟩ := hsec k H hH U D i q hi hUs hUc hU hn hfppf hD
  exact maximalToriAreConjugate_of_section_of_isUnipotent hH hU hn hfppf.2.2.2 hD σ hσ

/-- **Milne 2017, Theorem 16.33(d)**, from the existence of the split torus quotient with
unipotent kernel (Theorem 16.33(a), (c)) and of a homomorphic section of it
(Theorem 16.26(a)). -/
theorem solvableMaximalTorusSemidirectStatement_of_solvableTorusQuotient
    (hquot : SolvableTorusQuotientStatement.{u}) (hsec : SolvableSplitExtensionStatement.{u}) :
    SolvableMaximalTorusSemidirectStatement.{u} := by
  intro k _ _ H _ _ _ hH T s hs
  obtain ⟨U, D, i, q, hi, hUs, hUc, hU, hn, hfppf, hD⟩ := hquot k H hH
  obtain ⟨σ, hσ⟩ := hsec k H hH U D i q hi hUs hUc hU hn hfppf hD
  have hq := hfppf.2.2.2
  have := isIso_comp_of_section_of_isUnipotent hH hU hn hq hD σ hσ s hs
  have : Mono i.hom.hom := by
    have : Mono i.hom.hom.left := hi.mono
    exact Over.mono_of_mono_left _
  have := isIso_subgroupMultiplication_of_isIso_comp (s := s) this hq
  exact ⟨U, i, hi, hUs, hUc, hU, hn,
    fun W w _ hW => range_le_of_isUnipotent_of_isSplitTorus hD hq w hW,
    (isIso_subgroupMultiplication_reverse_iff s i).1 this⟩

end Langlands.GroupScheme
