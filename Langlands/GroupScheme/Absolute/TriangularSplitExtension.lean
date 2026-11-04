import Langlands.GroupScheme.Absolute.TriangularTorusLift
import Langlands.GroupScheme.Absolute.SolvableSplitExtensionStatement
import Langlands.GroupScheme.Absolute.SolvableTriangularEmbeddingProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitStatement
import Langlands.GroupScheme.SplitUnipotentQuotientSection
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.Examples.QuasiSplitUnitarySplitTorus
import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition
import Langlands.GroupScheme.Torus.UnipotentHom
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Group sections of solvable extensions of split tori -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.TriangularLayer

open PointedCoordinateWeights

/-- A triangular matrix whose diagonal part is trivial is unitriangular. -/
theorem mem_W_of_diagPart_eq_one {A : Type*} [CommRing A] {N : ℕ} {g : upper A N}
    (hg : diagPart A N g = 1) : (g : GL (Fin N) A) ∈ W A N 0 := by
  rw [mem_W]
  intro i j hij
  rw [Matrix.sub_apply]
  rcases lt_or_eq_of_le (show (j : ℕ) ≤ i by omega) with h | h
  · have h' : j < i := Fin.lt_def.2 h
    rw [mem_upper.1 g.2 i j h', Matrix.one_apply_ne (ne_of_lt h').symm, sub_zero]
  · have h' : j = i := Fin.ext h
    subst h'
    rw [← diagPart_apply_self, hg, Units.val_one, sub_self]

variable {k : Type u} [Field k] {N : ℕ}

/-! ### Affine points of the upper triangular group scheme -/

section Points

variable (k N) in
/-- The upper triangular group scheme over `k`: the block parabolic subgroup scheme of `GL_N`
for the decreasing weights `i ↦ -i`. -/
abbrev upperScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k) (fun i => -(i.val : ℤ))

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

variable (A) in
/-- The matrix of an affine point of the upper triangular group scheme. -/
def upperMatrix : Lie.AffinePoints (upperScheme k N) A →* GL (Fin N) A where
  toFun x := GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
    (CommAlgCat.of (CommRingCat.of k) A)
    (x ≫ (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _).hom.hom)
  map_one' := by rw [MonObj.one_comp, map_one]
  map_mul' x y := by rw [MonObj.mul_comp, map_mul]

theorem upperMatrix_apply (x : Lie.AffinePoints (upperScheme k N) A) :
    upperMatrix A x = GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
      (CommAlgCat.of (CommRingCat.of k) A)
      (x ≫ (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _).hom.hom) :=
  rfl

theorem upperMatrix_naturality (φ : A →ₐ[k] B) (x : Lie.AffinePoints (upperScheme k N) A) :
    upperMatrix B (Lie.affineMap _ φ x) =
      Matrix.GeneralLinearGroup.map (φ : A →+* B) (upperMatrix A x) := by
  have h := GeneralLinear.affinePointsEquiv_naturality (n := Fin N) (R := CommRingCat.of k)
    (S := CommAlgCat.of (CommRingCat.of k) A) (T := CommAlgCat.of (CommRingCat.of k) B)
    (CommAlgCat.ofHom φ)
    (x ≫ (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _).hom.hom)
  rw [upperMatrix_apply, upperMatrix_apply, Lie.affineMap_apply, Category.assoc, h]
  rfl

theorem upperMatrix_mem_upper (x : Lie.AffinePoints (upperScheme k N) A) :
    upperMatrix A x ∈ upper A N := by
  rw [upperMatrix_apply]
  change Corepresented.affinePointsEquiv _ _ _ (x ≫ (Corepresented.groupSchemeMap _ _
    (Corepresented.cutInclusion _)).hom.hom) ∈ _
  rw [Corepresented.groupSchemeMap_affinePoints]
  exact (Corepresented.affinePointsEquiv _ _ _ x).2

/-- The matrix of an affine point is the matrix of the point over the global sections,
transported along the global-sections isomorphism. -/
theorem upperMatrix_eq_map (x : Lie.AffinePoints (upperScheme k N) A) :
    upperMatrix A x = Matrix.GeneralLinearGroup.map
      (Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of k) A)).hom.hom.toRingHom
      (GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k) _
        (x ≫ (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _).hom.hom)) := by
  have hc : (Corepresented.affineSectionsIso
        (CommAlgCat.of (CommRingCat.of k) A)).hom.hom.toRingHom.comp
      (Corepresented.affineSectionsIso
        (CommAlgCat.of (CommRingCat.of k) A)).inv.hom.toRingHom = RingHom.id _ := by
    ext a
    exact congrArg (fun f => CommAlgCat.Hom.hom f a)
      (Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of k) A)).inv_hom_id
  rw [GeneralLinear.pointsEquiv_eq_affinePointsEquiv, ← Matrix.GeneralLinearGroup.map_comp_apply,
    ← Matrix.GeneralLinearGroup.map_comp, hc, Matrix.GeneralLinearGroup.map_id]
  rfl

/-- A point of the upper triangular group with trivial diagonal limit is unitriangular. -/
theorem upperMatrix_mem_W (x : Lie.AffinePoints (upperScheme k N) A)
    (hx : x ≫ (GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) _).hom.hom = 1) :
    upperMatrix A x ∈ W A N 0 := by
  have h := GeneralLinear.pointsEquiv_blockLimitHom (Fin N) (CommRingCat.of k)
    (fun i : Fin N => -(i.val : ℤ)) x
  rw [hx, MonObj.one_comp, map_one] at h
  rw [upperMatrix_eq_map]
  exact map_mem_W (mem_W_of_diagPart_eq_one h.symm) _

/-- Distinct weights make the diagonal subgroup scheme a split torus. -/
theorem isSplitTorus_blockLeviScheme :
    IsSplitTorus (GeneralLinear.blockLeviScheme (Fin N) (CommRingCat.of k)
      (fun i : Fin N => -(i.val : ℤ))) := by
  have he : Function.Injective (fun i : Fin N => -(i.val : ℤ)) := by
    intro i l h
    apply Fin.ext
    exact Int.ofNat_inj.mp (neg_injective h)
  exact ⟨ULift.{u} (Fin N), inferInstance,
    ⟨(GeneralLinear.diagonalTorusIso _ he (CommRingCat.of k)).symm⟩⟩

end Points

/-! ### The triangular lift attached to a scheme section -/

section Lift

variable (I : Type u) [Fintype I] [DecidableEq I]
  {H U : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ H)
  (q : H ⟶ splitTorus (Spec (CommRingCat.of k)) I) (j : H ⟶ upperScheme k N)
  (s : (splitTorus (Spec (CommRingCat.of k)) I).X ⟶ H.X)

local notation "𝔻" => splitTorus (Spec (CommRingCat.of k)) I

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

variable (A) in
/-- The matrix of an affine point of `H` under the triangular embedding. -/
def matrixOf : Lie.AffinePoints H A →* GL (Fin N) A where
  toFun h := upperMatrix A (h ≫ j.hom.hom)
  map_one' := by rw [MonObj.one_comp, map_one]
  map_mul' x y := by rw [MonObj.mul_comp, map_mul]

theorem matrixOf_apply (h : Lie.AffinePoints H A) :
    matrixOf j A h = upperMatrix A (h ≫ j.hom.hom) :=
  rfl

theorem matrixOf_naturality (φ : A →ₐ[k] B) (h : Lie.AffinePoints H A) :
    matrixOf j B (Lie.affineMap _ φ h) =
      Matrix.GeneralLinearGroup.map (φ : A →+* B) (matrixOf j A h) := by
  rw [matrixOf_apply, matrixOf_apply, ← upperMatrix_naturality, Lie.affineMap_apply,
    Lie.affineMap_apply, Category.assoc]

theorem matrixOf_injective [Mono j.hom.hom] : Function.Injective (matrixOf j A) := by
  have : Mono (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k)
      (fun i : Fin N => -(i.val : ℤ))).hom.hom :=
    Corepresented.mono_cutHom _
  intro x y h
  have h' := (GeneralLinear.affinePointsEquiv (Fin N) (CommRingCat.of k)
    (CommAlgCat.of (CommRingCat.of k) A)).injective h
  exact (cancel_mono j.hom.hom).1 ((cancel_mono (GeneralLinear.blockParabolicHom (Fin N)
    (CommRingCat.of k) (fun i : Fin N => -(i.val : ℤ))).hom.hom).1 h')

variable (A) in
/-- The affine point of the split torus with given unit coordinates. -/
abbrev torusPoint (t : I → Aˣ) : Lie.AffinePoints 𝔻 A :=
  (splitTorus.algebraPointsEquiv I A).symm t

omit [DecidableEq I] in
theorem torusPoint_naturality (φ : A →ₐ[k] B) (t : I → Aˣ) :
    Lie.affineMap _ φ (torusPoint I A t) =
      torusPoint I B (fun l => Units.map φ.toMonoidHom (t l)) := by
  apply (splitTorus.algebraPointsEquiv I B).injective
  rw [splitTorus.algebraPointsEquiv_naturality, MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply]

/-- The test scheme of an algebra. -/
abbrev specOf (A : Type u) [CommRing A] [Algebra k A] : Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of (CommRingCat.of k) A))

/-- The upper triangular lift of torus points through a scheme section of the quotient map,
with kernel the matrices of the points of the unipotent normal subgroup. -/
def torusLift (hU : IsUnipotent U) (hn : (SubgroupFunctor.range i).IsNormal)
    (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ H.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1)
    (hs : s ≫ q.hom.hom = 𝟙 _) : TorusLift k I N where
  lift A _ _ t := matrixOf j A (torusPoint I A t ≫ s)
  kernel A _ _ := ((SubgroupFunctor.range i).carrier (specOf A)).map (matrixOf j A)
  lift_naturality A B _ _ _ _ φ t := by
    rw [← torusPoint_naturality, ← matrixOf_naturality, Lie.affineMap_apply,
      Lie.affineMap_apply, Category.assoc]
  map_mem_kernel A B _ _ _ _ φ x hx := by
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2
      ⟨(algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom φ).op ≫ h,
        (SubgroupFunctor.range i).comp_mem
          ((algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom φ).op) hh, ?_⟩
    rw [← Lie.affineMap_apply]
    exact matrixOf_naturality j φ h
  lift_mem_upper A _ _ t := upperMatrix_mem_upper _
  kernel_le A _ _ := by
    rintro _ ⟨h, hh, rfl⟩
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.1 hh
    apply upperMatrix_mem_W
    have h1 := hU.comp_eq_one_of_isSplitTorus isSplitTorus_blockLeviScheme
      (i ≫ j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) _) (specOf A) y
    simpa only [Grp.comp_hom_hom, Category.assoc] using h1
  lift_mul_mem A _ _ t t' := by
    refine Subgroup.mem_map.2 ⟨((torusPoint I A t ≫ s) * (torusPoint I A t' ≫ s))⁻¹ *
      (torusPoint I A (t * t') ≫ s), ?_, by rw [map_mul, map_inv, map_mul]⟩
    rw [hker, MonObj.mul_comp, GrpObj.inv_comp, MonObj.mul_comp, Category.assoc, Category.assoc,
      Category.assoc, hs, Category.comp_id, Category.comp_id, Category.comp_id]
    exact inv_mul_eq_one.2 (map_mul (splitTorus.algebraPointsEquiv I A).symm t t').symm
  conj_mem A _ _ t x hx := by
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨(torusPoint I A t ≫ s)⁻¹ * h * (torusPoint I A t ≫ s), ?_,
      by rw [map_mul, map_mul, map_inv]⟩
    have h1 := hn _ (torusPoint I A t ≫ s)⁻¹ h (Subgroup.mem_top _) hh
    rwa [inv_inv] at h1

end Lift

/-! ### The group section -/

section Section

variable [IsAlgClosed k] (I : Type u) [Fintype I] [DecidableEq I]
  {H U : GroupScheme (Spec (CommRingCat.of k))} (i : U ⟶ H)
  (q : H ⟶ splitTorus (Spec (CommRingCat.of k)) I) (j : H ⟶ upperScheme k N)
  (s : (splitTorus (Spec (CommRingCat.of k)) I).X ⟶ H.X)
  (hU : IsUnipotent U) (hn : (SubgroupFunctor.range i).IsNormal)
  (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ H.X),
    g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1)
  (hs : s ≫ q.hom.hom = 𝟙 _)

include i q j s hU hn hker hs

local notation "𝔻" => splitTorus (Spec (CommRingCat.of k)) I
local notation "𝓛" => torusLift I i q j s hU hn hker hs

variable {A B : Type u} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]

/-- The unitriangular matrix conjugating the diagonal part of the lift into the lift modulo
the kernel. -/
def corrector : GL (Fin N) k :=
  Classical.choose (𝓛).exists_deviation_mem

theorem deviation_corrector_mem (t : I → Aˣ) :
    (𝓛).deviation (corrector I i q j s hU hn hker hs) t ∈ (𝓛).kernel A :=
  (Classical.choose_spec (𝓛).exists_deviation_mem).2 A t

/-- The point of the unipotent normal subgroup whose matrix is the deviation. -/
def deviationPoint (τ : Lie.AffinePoints (𝔻) A) : Lie.AffinePoints H A :=
  Classical.choose (Subgroup.mem_map.1
    (deviation_corrector_mem I i q j s hU hn hker hs (splitTorus.algebraPointsEquiv I A τ)))

theorem deviationPoint_mem (τ : Lie.AffinePoints (𝔻) A) :
    deviationPoint I i q j s hU hn hker hs τ ∈ (SubgroupFunctor.range i).carrier (specOf A) :=
  (Classical.choose_spec (Subgroup.mem_map.1
    (deviation_corrector_mem I i q j s hU hn hker hs (splitTorus.algebraPointsEquiv I A τ)))).1

theorem matrixOf_deviationPoint (τ : Lie.AffinePoints (𝔻) A) :
    matrixOf j A (deviationPoint I i q j s hU hn hker hs τ) =
      (𝓛).deviation (corrector I i q j s hU hn hker hs) (splitTorus.algebraPointsEquiv I A τ) :=
  (Classical.choose_spec (Subgroup.mem_map.1
    (deviation_corrector_mem I i q j s hU hn hker hs (splitTorus.algebraPointsEquiv I A τ)))).2

/-- The scheme section corrected by the deviation point. -/
def sectionPoint (τ : Lie.AffinePoints (𝔻) A) : Lie.AffinePoints H A :=
  (τ ≫ s) * (deviationPoint I i q j s hU hn hker hs τ)⁻¹

local notation "σ" => sectionPoint I i q j s hU hn hker hs

theorem matrixOf_sectionPoint (τ : Lie.AffinePoints (𝔻) A) :
    matrixOf j A (σ τ) =
      (𝓛).correction (corrector I i q j s hU hn hker hs) (splitTorus.algebraPointsEquiv I A τ) := by
  have hl : (𝓛).lift A (splitTorus.algebraPointsEquiv I A τ) = matrixOf j A (τ ≫ s) := by
    change matrixOf j A ((splitTorus.algebraPointsEquiv I A).symm
      (splitTorus.algebraPointsEquiv I A τ) ≫ s) = _
    rw [MulEquiv.symm_apply_apply]
  rw [sectionPoint, map_mul, map_inv, matrixOf_deviationPoint, TorusLift.deviation, ← hl,
    mul_inv_rev, inv_inv, mul_inv_cancel_left]

theorem sectionPoint_comp (τ : Lie.AffinePoints (𝔻) A) : σ τ ≫ q.hom.hom = τ := by
  rw [sectionPoint, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hs, Category.comp_id,
    (hker _ _).1 (deviationPoint_mem I i q j s hU hn hker hs τ), inv_one, mul_one]

variable [Mono j.hom.hom]

theorem sectionPoint_mul (τ τ' : Lie.AffinePoints (𝔻) A) : σ (τ * τ') = σ τ * σ τ' := by
  apply matrixOf_injective j
  rw [map_mul, matrixOf_sectionPoint, matrixOf_sectionPoint, matrixOf_sectionPoint, map_mul,
    TorusLift.correction_mul]

theorem sectionPoint_naturality (φ : A →ₐ[k] B) (τ : Lie.AffinePoints (𝔻) A) :
    Lie.affineMap H φ (σ τ) = σ (Lie.affineMap _ φ τ) := by
  apply matrixOf_injective j
  rw [matrixOf_naturality, matrixOf_sectionPoint, matrixOf_sectionPoint,
    TorusLift.correction_naturality, splitTorus.algebraPointsEquiv_naturality]

attribute [local instance] isAffineHom_splitTorus_spec

/-- The corrected section as a morphism of schemes. -/
def sectionHom : (𝔻).X ⟶ H.X :=
  homOfAffinePoints fun _ _ _ τ => σ τ

theorem comp_sectionHom (τ : Lie.AffinePoints (𝔻) A) :
    τ ≫ sectionHom I i q j s hU hn hker hs = σ τ :=
  comp_homOfAffinePoints _
    (fun _ _ _ _ _ _ f v => sectionPoint_naturality I i q j s hU hn hker hs f v) τ

theorem sectionHom_mul_universal :
    (fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) ≫ sectionHom I i q j s hU hn hker hs =
      (fst (𝔻).X (𝔻).X ≫ sectionHom I i q j s hU hn hker hs) *
        (snd (𝔻).X (𝔻).X ≫ sectionHom I i q j s hU hn hker hs) := by
  apply affine_hom_ext
  intro A _ _ v
  simp only [← Category.assoc, MonObj.comp_mul, comp_sectionHom]
  exact sectionPoint_mul I i q j s hU hn hker hs _ _

theorem sectionHom_mul {T : Over (Spec (CommRingCat.of k))} (x y : T ⟶ (𝔻).X) :
    (x * y) ≫ sectionHom I i q j s hU hn hker hs =
      (x ≫ sectionHom I i q j s hU hn hker hs) * (y ≫ sectionHom I i q j s hU hn hker hs) := by
  have hxy : x * y = lift x y ≫ (fst (𝔻).X (𝔻).X * snd (𝔻).X (𝔻).X) := by
    rw [MonObj.comp_mul, lift_fst, lift_snd]
  rw [hxy, Category.assoc, sectionHom_mul_universal, MonObj.comp_mul]
  simp only [← Category.assoc, lift_fst, lift_snd]

theorem sectionHom_comp : sectionHom I i q j s hU hn hker hs ≫ q.hom.hom = 𝟙 (𝔻).X := by
  apply affine_hom_ext
  intro A _ _ τ
  rw [← Category.assoc, comp_sectionHom, sectionPoint_comp, Category.comp_id]

/-- **The group section.** A homomorphic section of the quotient of a group with an upper
triangular embedding by a unipotent normal subgroup onto a split torus, built from a scheme
section of the quotient map. -/
def splitSection : 𝔻 ⟶ H :=
  homOfPoints (fun _ => MonoidHom.mk' (· ≫ sectionHom I i q j s hU hn hker hs)
    (sectionHom_mul I i q j s hU hn hker hs))
    (fun _ _ => by simp only [MonoidHom.mk'_apply, Category.assoc])

theorem splitSection_comp : splitSection I i q j s hU hn hker hs ≫ q = 𝟙 𝔻 := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, splitSection, comp_homOfPoints, MonoidHom.mk'_apply,
    Category.assoc, sectionHom_comp, Grp.id_hom_hom]
  intro _ _ _ _
  simp only [MonoidHom.mk'_apply, Category.assoc]

end Section

end TriangularLayer

open RelativeRoot in
/-- A group with a closed upper triangular embedding, a unipotent normal subgroup, and an fppf
quotient by it onto a split torus admitting a scheme section has a homomorphic section of the
quotient map. -/
theorem IsSplitTorus.exists_section_of_triangular {k : Type u} [Field k] [IsAlgClosed k]
    {H U D : GroupScheme (Spec (CommRingCat.of k))} {N : ℕ}
    (i : U ⟶ H) (q : H ⟶ D) (j : H ⟶ TriangularLayer.upperScheme k N) [Mono j.hom.hom]
    (hD : IsSplitTorus D) (hU : IsUnipotent U) (hn : (SubgroupFunctor.range i).IsNormal)
    (hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ H.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1)
    (s : D.X ⟶ H.X) (hs : s ≫ q.hom.hom = 𝟙 _) :
    ∃ σ : D ⟶ H, σ ≫ q = 𝟙 D := by
  classical
  obtain ⟨I, hI, ⟨f⟩⟩ := hD
  have : Fintype I := Fintype.ofFinite I
  have hfi : f.hom.hom.hom ≫ f.inv.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, f.hom_inv_id, Grp.id_hom_hom]
  have hif : f.inv.hom.hom ≫ f.hom.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, f.inv_hom_id, Grp.id_hom_hom]
  have hker' : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ H.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ (q ≫ f.hom).hom.hom = 1 := by
    intro T g
    rw [hker, Grp.comp_hom_hom]
    constructor
    · intro h
      rw [← Category.assoc, h, MonObj.one_comp]
    · intro h
      rw [← Category.comp_id (g ≫ q.hom.hom), ← hfi, ← Category.assoc, Category.assoc g, h,
        MonObj.one_comp]
  have hs' : (f.inv.hom.hom ≫ s) ≫ (q ≫ f.hom).hom.hom = 𝟙 _ := by
    rw [Grp.comp_hom_hom, Category.assoc, ← Category.assoc s, hs, Category.id_comp, hif]
  have hσ := TriangularLayer.splitSection_comp I i (q ≫ f.hom) j (f.inv.hom.hom ≫ s) hU hn
    hker' hs'
  refine ⟨f.hom ≫ TriangularLayer.splitSection I i (q ≫ f.hom) j (f.inv.hom.hom ≫ s) hU hn
    hker' hs', ?_⟩
  have hσq : TriangularLayer.splitSection I i (q ≫ f.hom) j (f.inv.hom.hom ≫ s) hU hn
      hker' hs' ≫ q = f.inv := by
    rw [← Category.comp_id (_ ≫ q), ← f.hom_inv_id, ← Category.assoc, Category.assoc _ q, hσ,
      Category.id_comp]
  rw [Category.assoc, hσq, f.hom_inv_id]

/-- **Milne 2017, Theorem 16.26(a), conditional form.** If smooth connected unipotent groups
over perfect fields are split, then the torus quotient of every smooth connected solvable group
over an algebraically closed field by a smooth connected unipotent normal subgroup has a
homomorphic section. -/
theorem solvableSplitExtension_of_perfectFieldUnipotentSplit
    (hsplit : PerfectFieldUnipotentSplitStatement.{u}) : SolvableSplitExtensionStatement.{u} := by
  intro k _ _ H _ _ _ hH U D i q hi hUs hUc hU hn hq hD
  obtain ⟨N, j, hj⟩ := solvableTriangularEmbeddingStatement k H hH
  have : IsAffineHom U.X.hom := HomogeneousQuotient.affine_subgroup_of_closed H U i hi
  have : IsAffineHom D.X.hom := hD.isAffineHom
  have : Smooth U.X.hom := hUs
  have hUsplit := hsplit k U hUc hU
  obtain ⟨s, hs⟩ := HomogeneousQuotient.fppf_section_of_split_unipotent_torsors H U i
    splitUnipotentAffineTorsorStatement hi hUsplit D q hq
  have hker : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ H.X),
      g ∈ (SubgroupFunctor.range i).carrier T ↔ g ≫ q.hom.hom = 1 := by
    intro T g
    rw [← hq.2.2.2, mem_range_kernelι_iff]
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact IsSplitTorus.exists_section_of_triangular i q j hD hU hn hker s hs

end Langlands.GroupScheme
