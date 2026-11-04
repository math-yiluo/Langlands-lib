import Langlands.Group.LieKolchin.Triangularization
import Langlands.GroupScheme.Absolute.LieKolchinRationalTriangularizationStatement
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.SchemeActionFiniteTarget

/-! # Lie–Kolchin on rational points

The rational points of a group scheme over a field `k` carry the topology induced by their
locations in the underlying space. Postcomposition with any endomorphism of the underlying
scheme is continuous for it; for a connected group locally of finite type over an
algebraically closed field the points form a preconnected space (Jacobson property); and the
zero set of the evaluation of a global function is closed. These are exactly the hypotheses
of the abstract matrix Lie–Kolchin theorem `Langlands.LieKolchin.exists_triangularizing`,
which proves `LieKolchinRationalTriangularizationStatement`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix commutatorElement

namespace Langlands.GroupScheme

namespace RationalZariski

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))

/-- The location of a rational point in the underlying topological space. -/
def location (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) : H.X.left :=
  x.left (IsLocalRing.closedPoint k)

/-- The topology on rational points induced by their locations. -/
@[instance_reducible]
def topology : TopologicalSpace (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :=
  TopologicalSpace.induced (location H) inferInstance

/-- Evaluation of a global function at a rational point, with values in `k`. -/
def evaluation (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) : Γ(H.X.left, ⊤) →+* k :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom.comp x.left.appTop.hom

/-- Constant global functions. -/
def const : k →+* Γ(H.X.left, ⊤) :=
  H.X.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

variable {H}

theorem evaluation_const (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) (c : k) :
    evaluation H x (const H c) = c := by
  have hx : x.left ≫ H.X.hom = 𝟙 _ := Over.w x
  have h1 : ∀ y, x.left.appTop (H.X.hom.appTop y) = y := by
    intro y
    change (x.left ≫ H.X.hom).appTop y = y
    rw [hx]
    rfl
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    (x.left.appTop (H.X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c))) = c
  rw [h1]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) c

theorem location_comp (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) (φ : H.X ⟶ H.X) :
    location H (x ≫ φ) = φ.left (location H x) :=
  rfl

/-- Postcomposition with an endomorphism of the underlying scheme is continuous. -/
theorem continuous_comp (φ : H.X ⟶ H.X) :
    @Continuous _ _ (topology H) (topology H) (fun y => y ≫ φ) := by
  let _ := topology H
  exact continuous_induced_rng.2 (φ.left.continuous.comp continuous_induced_dom)

/-- Over an algebraically closed field, the locations of rational points are the closed
points. -/
theorem range_location [IsAlgClosed k] [LocallyOfFiniteType H.X.hom] :
    Set.range (location H) = closedPoints H.X.left := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact isClosed_singleton_rationalPoint x
  · intro hp
    refine ⟨(rationalPointEquivClosedPoint H.X).symm ⟨p, hp⟩, ?_⟩
    exact congrArg Subtype.val ((rationalPointEquivClosedPoint H.X).apply_symm_apply ⟨p, hp⟩)

/-- The rational points of a connected group locally of finite type over an algebraically
closed field are preconnected, by the Jacobson property. -/
theorem preconnectedSpace [IsAlgClosed k] [LocallyOfFiniteType H.X.hom]
    [ConnectedSpace H.X.left] : @PreconnectedSpace _ (topology H) := by
  let _ := topology H
  have : JacobsonSpace H.X.left := LocallyOfFiniteType.jacobsonSpace H.X.hom
  have hrange := range_location (H := H)
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  obtain ⟨U, hU, hUs⟩ := isOpen_induced_iff.1 hs.isOpen
  obtain ⟨V, hV, hVs⟩ := isOpen_induced_iff.1 hs.isClosed.isOpen_compl
  have hcl : ∀ Z : Set H.X.left, IsLocallyClosed Z → (∀ x, location H x ∉ Z) → Z = ∅ := by
    intro Z hZ hx
    by_contra hne
    obtain ⟨p, hpZ, hp⟩ := nonempty_inter_closedPoints (Set.nonempty_iff_ne_empty.2 hne) hZ
    rw [← hrange] at hp
    obtain ⟨x, rfl⟩ := hp
    exact hx x hpZ
  have hdisj : U ∩ V = ∅ := by
    refine hcl _ (hU.inter hV).isLocallyClosed fun x ⟨hxU, hxV⟩ => ?_
    have h1 : x ∈ s := hUs ▸ hxU
    have h2 : x ∈ sᶜ := hVs ▸ hxV
    exact h2 h1
  have hcover : (U ∪ V)ᶜ = ∅ := by
    refine hcl _ (hU.union hV).isClosed_compl.isLocallyClosed fun x hx => ?_
    refine hx ?_
    by_cases h : x ∈ s
    · exact Or.inl (show x ∈ location H ⁻¹' U from hUs ▸ h)
    · exact Or.inr (show x ∈ location H ⁻¹' V from hVs ▸ h)
  have hUc : Vᶜ = U := by
    ext p
    constructor
    · intro hp
      by_contra hpU
      have : p ∈ (U ∪ V)ᶜ := fun h => h.elim hpU hp
      rw [hcover] at this
      exact this
    · intro hpU hpV
      have : p ∈ U ∩ V := ⟨hpU, hpV⟩
      rw [hdisj] at this
      exact this
  have hUclopen : IsClopen U := ⟨hUc ▸ hV.isClosed_compl, hU⟩
  rcases isClopen_iff.1 hUclopen with h | h
  · left
    rw [← hUs, h, Set.preimage_empty]
  · right
    rw [← hUs, h, Set.preimage_univ]

/-- The zero set of the evaluation of a global function is closed. -/
theorem isClosed_evaluation_eq_zero (s : Γ(H.X.left, ⊤)) :
    @IsClosed _ (topology H) {x | evaluation H x s = 0} := by
  let _ := topology H
  have hset : {x | evaluation H x s = 0} =
      location H ⁻¹' (H.X.left.basicOpen s : Set H.X.left)ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe]
    let e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
    have hmem : location H x ∈ H.X.left.basicOpen s ↔
        IsLocalRing.closedPoint k ∈
          (Spec (CommRingCat.of k)).basicOpen (x.left.appTop s) := by
      rw [← Scheme.preimage_basicOpen_top]
      rfl
    rw [hmem]
    have hev : evaluation H x s = e (x.left.appTop s) := rfl
    rw [hev, map_eq_zero_iff e e.injective]
    constructor
    · intro h0
      rw [h0, Scheme.basicOpen_zero]
      exact fun h => h
    · intro hmem'
      by_contra h0
      have hunit : IsUnit (x.left.appTop s) :=
        (isUnit_map_iff e _).1 (IsUnit.mk0 _ ((map_ne_zero_iff e e.injective).2 h0))
      have hU := Scheme.basicOpen_of_isUnit (Spec (CommRingCat.of k)) hunit
      exact hmem' (by rw [hU]; trivial)
  rw [hset]
  exact (H.X.left.basicOpen s).isOpen.isClosed_compl.preimage continuous_induced_dom

end RationalZariski

open RationalZariski

namespace MatrixRepresentation

variable {k : Type u} [Field k] {H : GroupScheme (Spec (CommRingCat.of k))}
  {N : ℕ}

/-- The rational matrix of a representation as a monoid homomorphism into matrices. -/
def rationalMatrixMonoidHom (ρ : MatrixRepresentation H (Fin N)) :
    (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) →* Matrix (Fin N) (Fin N) k :=
  (Units.coeHom _).comp ρ.rationalMatrix

/-- Each rational matrix entry is the evaluation of a global function. -/
theorem rationalMatrixMonoidHom_apply_apply (ρ : MatrixRepresentation H (Fin N))
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) (i j : Fin N) :
    ρ.rationalMatrixMonoidHom x i j =
      evaluation H x (ρ.hom.hom.left.appTop (GeneralLinear.entrySection (Fin N) _ i j)) := by
  change (ρ.rationalMatrix x : Matrix (Fin N) (Fin N) k) i j = _
  rw [rationalMatrix_apply_apply]
  rfl

/-- Linear conditions on the rational matrices define closed sets of rational points. -/
theorem isClosed_rationalMatrix_linear (ρ : MatrixRepresentation H (Fin N))
    (Λ : Matrix (Fin N) (Fin N) k →ₗ[k] k) (c : k) :
    @IsClosed _ (topology H) {x | Λ (ρ.rationalMatrixMonoidHom x) = c} := by
  let s : Fin N → Fin N → Γ(H.X.left, ⊤) := fun i j =>
    ρ.hom.hom.left.appTop (GeneralLinear.entrySection (Fin N) _ i j)
  let t : Γ(H.X.left, ⊤) :=
    ∑ i, ∑ j, s i j * const H (Λ (Matrix.single i j 1)) - const H c
  have hset : {x | Λ (ρ.rationalMatrixMonoidHom x) = c} = {x | evaluation H x t = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    have hΛ : Λ (ρ.rationalMatrixMonoidHom x) =
        ∑ i, ∑ j, ρ.rationalMatrixMonoidHom x i j * Λ (Matrix.single i j 1) := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single (ρ.rationalMatrixMonoidHom x)]
      simp only [map_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
    have hev : evaluation H x t = Λ (ρ.rationalMatrixMonoidHom x) - c := by
      simp only [t, map_sub, map_sum, map_mul, evaluation_const, hΛ, s,
        rationalMatrixMonoidHom_apply_apply]
    rw [hev, sub_eq_zero]
  rw [hset]
  exact isClosed_evaluation_eq_zero t

end MatrixRepresentation

open MatrixRepresentation

/-- **Lie–Kolchin on rational points.** Every representation of a smooth connected affine
group over an algebraically closed field whose rational points form a solvable group can be
conjugated so that all rational-point matrices are upper triangular. -/
theorem lieKolchinRationalTriangularization :
    LieKolchinRationalTriangularizationStatement.{u} := by
  intro k _ _ H _ _ _ hsolv N ρ
  let _ := topology H
  have : PreconnectedSpace (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :=
    preconnectedSpace (H := H)
  have hmul : ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X,
      Continuous fun x => a * x := by
    intro a
    obtain ⟨φ, hφ⟩ := exists_comp_eq_mul_left a
    have : (fun x => a * x) = fun y => y ≫ φ := funext fun y => (hφ y).symm
    rw [this]
    exact continuous_comp φ
  have hinv : Continuous fun x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X => x⁻¹ := by
    have : (fun x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X => x⁻¹) =
        fun y => y ≫ (𝟙 H.X)⁻¹ := by
      funext y
      rw [GrpObj.comp_inv, Category.comp_id]
    rw [this]
    exact continuous_comp _
  have hcomm : ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X,
      Continuous fun x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X => ⁅a, x⁆ := by
    intro a
    obtain ⟨φ, hφ⟩ := exists_comp_eq_commutator_left a
    have : (fun x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X => ⁅a, x⁆) =
        fun y => y ≫ φ :=
      funext fun y => (hφ y).symm
    rw [this]
    exact continuous_comp φ
  obtain ⟨P, Q, hPQ, htri⟩ := Langlands.LieKolchin.exists_triangularizing hmul hinv hcomm N
    ρ.rationalMatrixMonoidHom (isClosed_rationalMatrix_linear ρ)
  have hQP : Q * P = 1 := mul_eq_one_comm.1 hPQ
  let C : GL (Fin N) k := ⟨Q, P, hQP, hPQ⟩
  let e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  refine ⟨(GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k)
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm
      (Matrix.GeneralLinearGroup.map e.symm.toRingHom C), fun x i j hji => ?_⟩
  have ha : ((Matrix.GeneralLinearGroup.map e.symm.toRingHom C :
      GL (Fin N) Γ(Spec (CommRingCat.of k), ⊤)) : Matrix (Fin N) (Fin N) _).map e = Q := by
    ext a b
    rw [Matrix.map_apply, Matrix.GeneralLinearGroup.map_apply]
    exact e.apply_symm_apply _
  have hb : (ρ.pointMatrix (Over.mk (𝟙 (Spec (CommRingCat.of k)))) x).val.map e =
      ρ.rationalMatrixMonoidHom x := by
    ext a b
    rfl
  have hc : (((Matrix.GeneralLinearGroup.map e.symm.toRingHom C)⁻¹ :
      GL (Fin N) Γ(Spec (CommRingCat.of k), ⊤)) : Matrix (Fin N) (Fin N) _).map e = P := by
    ext a b
    rw [Matrix.map_apply, ← map_inv, Matrix.GeneralLinearGroup.map_apply]
    exact e.apply_symm_apply _
  have key : ((ρ.conjugate ((GeneralLinear.pointsEquiv (Fin N) (CommRingCat.of k)
      (Over.mk (𝟙 (Spec (CommRingCat.of k))))).symm
      (Matrix.GeneralLinearGroup.map e.symm.toRingHom C))).pointMatrix
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) x).val.map e =
      Q * ρ.rationalMatrixMonoidHom x * P := by
    rw [conjugate_pointMatrix, constantPoint_self, MulEquiv.apply_symm_apply,
      Units.val_mul, Units.val_mul, ← ha, ← hb, ← hc]
    exact (Matrix.map_mul (f := e.toRingHom)).trans
      (congrArg (· * _) (Matrix.map_mul (f := e.toRingHom)))
  have h := congrFun (congrFun key i) j
  rw [Matrix.map_apply, htri x i j hji] at h
  exact (map_eq_zero_iff e e.injective).1 h

end Langlands.GroupScheme
