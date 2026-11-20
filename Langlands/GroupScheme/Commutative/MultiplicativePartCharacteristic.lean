import Langlands.GroupScheme.Torus.ConnectedQuotientCommutative
import Langlands.GroupScheme.Commutative.MultiplicativePartExistence
import Langlands.GroupScheme.MatrixRepresentation.DiagonalizableCharacterDecomposition
import Langlands.GroupScheme.Rational.UnipotentCompactSubgroups
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # Homomorphisms from multiplicative-type to unipotent groups after base change

For a group `S` of multiplicative type and an affine unipotent group `Q` of finite type over a
field `k`, every homomorphism `S_R ⟶ Q_R` over an arbitrary `k`-algebra `R` is trivial. As a
consequence, the kernel of an fppf quotient of `G` onto `Q` with multiplicative-type kernel is
stable under every automorphism of `G_R` (the characteristic clause of Milne 2017,
Theorem 16.13(a)). -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix TensorProduct

namespace Langlands.GroupScheme

namespace CommutativeDecomposition

section Unitriangular

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)} {n : ℕ}

/-- Every point matrix of the representation is upper unitriangular. -/
def PointUnitriangular (ρ : MatrixRepresentation G (Fin n)) : Prop :=
  ∀ (T : Over (Spec R)) (x : T ⟶ G.X) (i j : Fin n), j ≤ i →
    (ρ.pointMatrix T x : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) i j =
      (1 : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) i j

/-- Point unitriangularity is preserved by restriction along any homomorphism. -/
theorem PointUnitriangular.restrict {ρ : MatrixRepresentation G (Fin n)}
    (h : PointUnitriangular ρ) (f : H ⟶ G) : PointUnitriangular (f ≫ ρ) := by
  intro T x i j hij
  change ((ρ.restrict f).pointMatrix T x : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) i j = _
  rw [MatrixRepresentation.pointMatrix_restrict]
  exact h T _ i j hij

/-- Point unitriangularity is preserved by arbitrary base change, with the canonical
identification of the base change of `GL_n`. -/
theorem PointUnitriangular.baseChange {R' : CommRingCat.{u}} (b : Spec R' ⟶ Spec R)
    {ρ : MatrixRepresentation G (Fin n)} (h : PointUnitriangular ρ) :
    PointUnitriangular ((GroupScheme.baseChange b).map ρ ≫
      (GeneralLinear.baseChangeIso (Fin n) b).hom) := by
  intro T x i j hij
  have key : MatrixRepresentation.pointMatrix ((GroupScheme.baseChange b).map ρ ≫
      (GeneralLinear.baseChangeIso (Fin n) b).hom) T x =
        ρ.pointMatrix ((Over.map b).obj T) (baseChangePointsEquiv b G T x) := by
    rw [MatrixRepresentation.pointMatrix_apply, MatrixRepresentation.pointMatrix_apply,
      Grp.comp_hom_hom, ← Category.assoc, GeneralLinear.baseChangeIso, comp_isoOfPoints_hom]
    simp only [GeneralLinear.baseChangeGLPointsEquiv, MulEquiv.trans_apply,
      MulEquiv.apply_symm_apply, baseChangePointsEquiv_comp]
  rw [key]
  exact h _ _ i j hij

end Unitriangular

section UnipotentRepresentation

variable {k : Type u} [Field k]

/-- A unipotent affine group scheme of finite type over a field has a closed matrix
representation all of whose point matrices are upper unitriangular. -/
theorem exists_closed_pointUnitriangular
    (U : GroupScheme (Spec (CommRingCat.of k))) [IsAffine U.X.left]
    [LocallyOfFiniteType U.X.hom] (hU : IsUnipotent U) :
    ∃ (n : ℕ) (ρ : MatrixRepresentation U (Fin n)), IsClosedSubgroup ρ ∧
      PointUnitriangular ρ := by
  let A := AffineCoordinates.hopfAlgebra U
  have : Algebra.FiniteType k A := AffineCoordinates.algebraFiniteType U
  obtain ⟨n, M, hcomul, hcounit, hgen, hdiag, hlow⟩ :=
    Algebra.GradedHopf.exists_unitriangular_matrixCoefficients A
      (IsUnipotent.of_iso (AffineCoordinates.hopfSpecIso U) hU)
  let e := AffineCoordinates.corepresentation U
  let M' : Matrix (Fin n) (Fin n) (AffineCoordinates.algebra U) := M
  have hcomul' : ∀ i j, AffineLinearEmbedding.comul e (M' i j) =
      ∑ l, M' i l ⊗ₜ[CommRingCat.of k] M' l j := fun i j =>
    (LinearMap.congr_fun (AffineCoordinates.corepresentation_comul U) (M i j)).trans
      (hcomul i j)
  have hcounit' : ∀ i j, AffineLinearEmbedding.counit e (M' i j) =
      (1 : Matrix (Fin n) (Fin n) (CommRingCat.of k)) i j := fun i j => by
    rw [Matrix.one_apply]
    exact (LinearMap.congr_fun (AffineCoordinates.corepresentation_counit U) (M i j)).trans
      (hcounit i j)
  let ρ : MatrixRepresentation U (Fin n) :=
    (AffineCoordinates.groupSchemeIso U).inv ≫ AffineLinearEmbedding.toGLHom e M' hcomul' hcounit'
  have hρ : IsClosedSubgroup ρ := by
    have hmodel := AffineLinearEmbedding.isClosedSubgroup_toGLHom e M' hcomul' hcounit' hgen
    have : IsIso (AffineCoordinates.groupSchemeIso U).inv.hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map
        (AffineCoordinates.groupSchemeIso U).inv.hom.hom))
    have : IsClosedImmersion
        (AffineLinearEmbedding.toGLHom e M' hcomul' hcounit').hom.hom.left := hmodel
    change IsClosedImmersion ((AffineCoordinates.groupSchemeIso U).inv.hom.hom.left ≫
      (AffineLinearEmbedding.toGLHom e M' hcomul' hcounit').hom.hom.left)
    infer_instance
  refine ⟨n, ρ, hρ, fun T x i j hij => ?_⟩
  rw [pointMatrix_toGLHom_apply U M' hcomul' hcounit']
  rcases eq_or_lt_of_le hij with h | h
  · subst h
    have hd : M' j j = 1 := hdiag j
    rw [hd, map_one, Matrix.one_apply_eq]
    rfl
  · have hl : M' i j = 0 := hlow i j h
    rw [hl, map_zero, Matrix.one_apply_ne (ne_of_gt h)]
    rfl

end UnipotentRepresentation

section Diagonalizable

open MatrixRepresentation.DiagonalizableCoefficients Diagonalizable.Averaging

variable {R : CommRingCat.{u}} (Λ : Type u) [AddCommGroup Λ] {n : ℕ}
  (ρ : MatrixRepresentation (Diagonalizable.groupScheme R Λ).toGrp (Fin n))

/-- If the universal matrix of a representation of `D(Λ)` is upper unitriangular, then all its
coefficient columns at nonzero characters vanish. -/
theorem coefficientColumn_eq_zero_of_unitriangular
    (hU : ∀ i j : Fin n, j ≤ i →
      (universalMatrix Λ ρ : Matrix (Fin n) (Fin n) (AddMonoidAlgebra R Λ)) i j =
        (1 : Matrix (Fin n) (Fin n) (AddMonoidAlgebra R Λ)) i j)
    {m : Λ} (hm : m ≠ 0) (j : Fin n) : coefficientColumn Λ ρ m j = 0 := by
  classical
  have hw := coefficientColumn_weight Λ ρ (A := AddMonoidAlgebra R Λ) (universalPoint R Λ) m j
  rw [pointsEquiv_universalPoint] at hw
  funext a
  induction a using WellFoundedGT.induction with
  | _ a ih =>
    have ha := congrFun hw a
    change (∑ b, (universalMatrix Λ ρ : Matrix (Fin n) (Fin n) (AddMonoidAlgebra R Λ)) a b *
        algebraMap R (AddMonoidAlgebra R Λ) (coefficientColumn Λ ρ m j b)) =
      (Diagonalizable.monomialUnits R Λ (.ofAdd m) : AddMonoidAlgebra R Λ) *
        algebraMap R (AddMonoidAlgebra R Λ) (coefficientColumn Λ ρ m j a) at ha
    rw [Finset.sum_eq_single a] at ha
    · rw [hU a a le_rfl, Matrix.one_apply_eq, one_mul, Diagonalizable.monomialUnits_val] at ha
      have h0 := congrArg (fun p : AddMonoidAlgebra R Λ => p.coeff 0) ha
      simp only [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
        AddMonoidAlgebra.single_mul_single, one_mul, Algebra.algebraMap_self, RingHom.id_apply,
        AddMonoidAlgebra.coeff_single, toAdd_ofAdd, add_zero] at h0
      simpa [Finsupp.single_apply, hm] using h0
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with h | h
      · rw [hU a b h.le, Matrix.one_apply_ne (Ne.symm hb), zero_mul]
      · rw [ih b h, Pi.zero_apply, map_zero, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h

/-- An upper unitriangular universal matrix of a representation of `D(Λ)` is the identity. -/
theorem universalMatrix_eq_one_of_unitriangular
    (hU : ∀ i j : Fin n, j ≤ i →
      (universalMatrix Λ ρ : Matrix (Fin n) (Fin n) (AddMonoidAlgebra R Λ)) i j =
        (1 : Matrix (Fin n) (Fin n) (AddMonoidAlgebra R Λ)) i j) :
    universalMatrix Λ ρ = 1 := by
  have hcoeff : ∀ (a b : Fin n) (m : Λ), m ≠ 0 →
      ((universalMatrix Λ ρ : Matrix (Fin n) (Fin n) (AddMonoidAlgebra R Λ)) a b).coeff m = 0 :=
    fun a b m hm => congrFun (coefficientColumn_eq_zero_of_unitriangular Λ ρ hU hm b) a
  have hsingle : ∀ a b : Fin n,
      (universalMatrix Λ ρ : Matrix (Fin n) (Fin n) (AddMonoidAlgebra R Λ)) a b =
        AddMonoidAlgebra.single 0
          (((universalMatrix Λ ρ : Matrix (Fin n) (Fin n) (AddMonoidAlgebra R Λ)) a b).coeff 0) := by
    intro a b
    ext m
    by_cases hm : m = 0
    · subst hm
      simp [AddMonoidAlgebra.coeff_single]
    · rw [hcoeff a b m hm, AddMonoidAlgebra.coeff_single]
      simp [Ne.symm hm]
  have hone := universalMatrix_evaluateOne Λ ρ
  refine Matrix.GeneralLinearGroup.ext fun a b => ?_
  have hab := congrArg (fun M : GL (Fin n) R => (M : Matrix (Fin n) (Fin n) R) a b) hone
  change (Diagonalizable.lift R Λ (B := CommAlgCat.of R R) (1 : Multiplicative Λ →* Rˣ)).hom
      ((universalMatrix Λ ρ : Matrix (Fin n) (Fin n) (AddMonoidAlgebra R Λ)) a b) =
    (1 : Matrix (Fin n) (Fin n) R) a b at hab
  rw [hsingle a b] at hab
  simp only [Diagonalizable.lift, CommAlgCat.hom_ofHom, AddMonoidAlgebra.lift_single, map_one,
    MonoidHom.one_apply, MonoidHom.comp_apply] at hab
  have hc : ((universalMatrix Λ ρ : Matrix (Fin n) (Fin n) (AddMonoidAlgebra R Λ)) a b).coeff 0 =
      (1 : Matrix (Fin n) (Fin n) R) a b := by
    simpa using hab
  rw [hsingle a b, hc, Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [AddMonoidAlgebra.one_def]

/-- A representation of `D(Λ)` whose universal matrix is the identity is trivial. -/
theorem eq_zero_of_universalMatrix_eq_one (h : universalMatrix Λ ρ = 1) : ρ = 0 := by
  apply eq_zero_of_hom_eq_one
  have h1 : GeneralLinear.affinePointsEquiv (Fin n) R _ (𝟙 _ ≫ ρ.hom.hom) =
      GeneralLinear.affinePointsEquiv (Fin n) R _ 1 := by
    rw [map_one]
    exact h
  have h2 := (GeneralLinear.affinePointsEquiv (Fin n) R _).injective h1
  exact (Category.id_comp _).symm.trans h2

/-- A representation of `D(Λ)` over any ring, all of whose point matrices are upper
unitriangular, is trivial. -/
theorem eq_zero_of_pointUnitriangular (h : PointUnitriangular ρ) : ρ = 0 := by
  apply eq_zero_of_universalMatrix_eq_one Λ ρ
  apply universalMatrix_eq_one_of_unitriangular Λ ρ
  intro i j hij
  have hp := h _ (universalPoint R Λ) i j hij
  rw [MatrixRepresentation.pointMatrix_eq_affineMatrix] at hp
  let e := Corepresented.affineSectionsIso (CommAlgCat.of R (AddMonoidAlgebra R Λ))
  let φ := e.inv.hom.toRingHom
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hx := congrArg (fun f => f.hom x) e.inv_hom_id
    have hy := congrArg (fun f => f.hom y) e.inv_hom_id
    simp only [CommAlgCat.hom_comp, AlgHom.comp_apply, CommAlgCat.hom_id,
      AlgHom.id_apply] at hx hy
    rw [← hx, ← hy]
    exact congrArg e.hom.hom hxy
  apply hinj
  rw [Matrix.one_apply, apply_ite φ, map_one, map_zero, ← Matrix.one_apply]
  exact hp

end Diagonalizable

section BaseChange

variable {k : Type u} [Field k]

/-- Let `S` be of multiplicative type and `Q` affine unipotent of finite type over a field `k`.
For every `k`-algebra `R`, every homomorphism `S_R ⟶ Q_R` is trivial. -/
theorem baseChange_hom_eq_zero {S Q : GroupScheme (Spec (CommRingCat.of k))}
    (hS : IsMultiplicativeType S) (hQ : IsUnipotent Q) [IsAffineHom Q.X.hom]
    [LocallyOfFiniteType Q.X.hom] (R : Type u) [CommRing R] [Algebra k R]
    (φ : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).obj S ⟶
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).obj Q) :
    φ = 0 := by
  have : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  obtain ⟨n, ρ, hρc, hρu⟩ := exists_closed_pointUnitriangular Q hQ
  obtain ⟨K, _, _, Λ, _, _, ⟨eD⟩⟩ := hS
  let b := Spec.map (CommRingCat.ofHom (algebraMap k R))
  let F := GroupScheme.baseChange b
  let m : F.obj Q ⟶ GeneralLinear.groupScheme (Fin n) (CommRingCat.of R) :=
    F.map ρ ≫ (GeneralLinear.baseChangeIso (Fin n) b).hom
  let ψ := φ ≫ m
  have hψ : PointUnitriangular ψ := (hρu.baseChange b).restrict φ
  -- the base change to `R ⊗[k] K`, over which `S` splits
  let R' := R ⊗[k] K
  let bK := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let c : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R R'))
  let c' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : K →ₐ[k] R').toRingHom)
  have hsq : c' ≫ bK = c ≫ b := by
    simp only [c, c', bK, b, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact ((Algebra.TensorProduct.includeRight : K →ₐ[k] R').commutes x).trans
      (IsScalarTower.algebraMap_apply k R R' x)
  let F' := GroupScheme.baseChange c
  let E : (Diagonalizable.groupScheme (CommRingCat.of R') Λ).toGrp ≅ F'.obj (F.obj S) :=
    (Diagonalizable.baseChangeIso c' Λ).symm ≪≫
      ((GroupScheme.baseChange c').mapIso eD).symm ≪≫ (Langlands.GroupScheme.baseChangeCompIso' bK c' S).symm ≪≫
      eqToIso (by rw [hsq]) ≪≫ Langlands.GroupScheme.baseChangeCompIso' b c S
  let ψ' := F'.map ψ ≫ (GeneralLinear.baseChangeIso (Fin n) c).hom
  have h0 : E.hom ≫ ψ' = 0 :=
    eq_zero_of_pointUnitriangular Λ (E.hom ≫ ψ') ((hψ.baseChange c).restrict E.hom)
  have h1 : F'.map ψ = 0 := by
    have h2 : ψ' = 0 := by
      rw [← cancel_epi E.hom, h0, comp_zero]
    rw [← cancel_mono (GeneralLinear.baseChangeIso (Fin n) c).hom, zero_comp]
    exact h2
  -- faithfully flat descent along `R → R ⊗[k] K`
  have hff : Flat c ∧ Surjective c :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R R'))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Flat c := hff.1
  have : Surjective c := hff.2
  have hψ0 : ψ = 0 := by
    apply (Grp.forget _).map_injective
    change ψ.hom.hom = (1 : _ ⟶ _)
    apply (Over.pullback c).map_injective
    rw [Functor.map_one]
    exact congrArg (fun j => j.hom.hom) h1
  -- `m` is a monomorphism
  have : IsClosedImmersion ρ.hom.hom.left := hρc
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  have : Mono (F.map ρ).hom.hom := inferInstanceAs (Mono ((Over.pullback b).map ρ.hom.hom))
  have : Mono m.hom.hom := inferInstanceAs (Mono ((F.map ρ).hom.hom ≫ _))
  have hφm : φ ≫ m = 0 ≫ m := by
    rw [zero_comp]
    exact hψ0
  have h3 : φ.hom.hom ≫ m.hom.hom = (0 : F.obj S ⟶ F.obj Q).hom.hom ≫ m.hom.hom :=
    congrArg (fun j => j.hom.hom) hφm
  apply (Grp.forget _).map_injective
  exact (cancel_mono m.hom.hom).mp h3

end BaseChange

section Characteristic

/-- Composing with a fixed homomorphism preserves inclusions of ranges. -/
theorem range_comp_le_range_comp {B : Scheme.{u}} {A A' G C : GroupScheme B} {f : A ⟶ G}
    {f' : A' ⟶ G} (h : SubgroupFunctor.range f ≤ SubgroupFunctor.range f') (g : G ⟶ C) :
    SubgroupFunctor.range (f ≫ g) ≤ SubgroupFunctor.range (f' ≫ g) := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hy : y ≫ f.hom.hom ∈ (SubgroupFunctor.range f).carrier T :=
    SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp (h T hy)
  refine SubgroupFunctor.mem_range.mpr ⟨z, ?_⟩
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, hz, Category.assoc]

/-- Let `q : G ⟶ Q` have kernel `range s`. After base change along `b`, every homomorphism
`φ` into `G` with `φ ≫ q = 0` has range inside the range of the base change of `s`. -/
theorem range_le_baseChange_of_comp_eq_zero {B B' : Scheme.{u}} (b : B' ⟶ B)
    {H G Q : GroupScheme B} {A : GroupScheme B'} (s : H ⟶ G) (q : G ⟶ Q)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range s)
    (φ : A ⟶ (GroupScheme.baseChange b).obj G)
    (hφ : φ ≫ (GroupScheme.baseChange b).map q = 0) :
    SubgroupFunctor.range φ ≤ SubgroupFunctor.range ((GroupScheme.baseChange b).map s) := by
  rw [SubgroupFunctor.range_baseChangeHom, ← hq, ← kernel_range_baseChange]
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  rw [mem_range_kernelι_iff, Category.assoc, ← Grp.comp_hom_hom, hφ]
  exact MonObj.comp_one y

variable {k : Type u} [Field k]

/-- **Characteristic clause.** Let `s : S ⟶ G` be a subgroup of multiplicative type over a
field `k` which is the kernel of a homomorphism `q : G ⟶ Q` to an affine unipotent group of
finite type. Then for every `k`-algebra `R`, every automorphism `α` of `G_R` maps `S_R` onto
itself: `range (s_R ≫ α) = range s_R`. -/
theorem range_baseChange_comp_iso {S G Q : GroupScheme (Spec (CommRingCat.of k))}
    (s : S ⟶ G) (q : G ⟶ Q) (hS : IsMultiplicativeType S)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range s) (hQ : IsUnipotent Q)
    [IsAffineHom Q.X.hom] [LocallyOfFiniteType Q.X.hom] (R : Type u) [CommRing R]
    [Algebra k R]
    (α : (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).obj G ≅
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).obj G) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).map s ≫
          α.hom) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))).map s) := by
  let F := GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  have key : ∀ β : F.obj G ⟶ F.obj G,
      SubgroupFunctor.range (F.map s ≫ β) ≤ SubgroupFunctor.range (F.map s) := fun β =>
    range_le_baseChange_of_comp_eq_zero _ s q hq (F.map s ≫ β)
      (baseChange_hom_eq_zero hS hQ R _)
  refine le_antisymm (key α.hom) ?_
  calc SubgroupFunctor.range (F.map s)
      = SubgroupFunctor.range ((F.map s ≫ α.inv) ≫ α.hom) := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ ≤ SubgroupFunctor.range (F.map s ≫ α.hom) := range_comp_le_range_comp (key α.inv) α.hom

/-- **Milne 2017, Theorem 16.13(a).** A commutative affine algebraic group `G` over a field `k`
has a closed subgroup `s : S ⟶ G` of multiplicative type containing every closed subgroup of
multiplicative type, stable under every automorphism of `G_R` for every `k`-algebra `R`, with
unipotent fppf quotient `q : G ⟶ Q`. -/
theorem exists_characteristic_multiplicativePart (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [IsCommMonObj G.X] :
    ∃ (S Q : GroupScheme (Spec (CommRingCat.of k))) (s : S ⟶ G) (q : G ⟶ Q),
      IsClosedSubgroup s ∧ IsMultiplicativeType S ∧
        (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
          IsClosedSubgroup h → IsMultiplicativeType H →
            SubgroupFunctor.range h ≤ SubgroupFunctor.range s) ∧
        (∀ (R : Type u) [CommRing R] [Algebra k R],
          let F := GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k R)))
          ∀ α : F.obj G ≅ F.obj G,
            SubgroupFunctor.range (F.map s ≫ α.hom) = SubgroupFunctor.range (F.map s)) ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range s) q ∧ IsUnipotent Q := by
  obtain ⟨S, Q, s, q, hs, hS, hmax, hq, hQ, hQl, hQa⟩ := exists_multiplicativePart G
  exact ⟨S, Q, s, q, hs, hS, hmax,
    fun R _ _ α => range_baseChange_comp_iso s q hS hq.2.2.2 hQ R α, hq, hQ⟩

end Characteristic

end CommutativeDecomposition

end Langlands.GroupScheme
