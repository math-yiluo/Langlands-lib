import Langlands.GroupScheme.MatrixRepresentationConjugate
import Langlands.GroupScheme.MatrixRepresentationRationalPoints
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.Reductive.GeneralLinearWeyl

/-! # Rational points of unipotent affine group schemes form a solvable group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace MatrixRepresentation

/-! ### Lower-right blocks of matrices fixing the first basis vector -/

section Tail

variable {S : Type*} [CommRing S] {m : ℕ}

/-- The lower-right `m × m` block of an `(m + 1) × (m + 1)` matrix. -/
def tail (M : Matrix (Fin (m + 1)) (Fin (m + 1)) S) : Matrix (Fin m) (Fin m) S :=
  M.submatrix Fin.succ Fin.succ

omit [CommRing S] in
@[simp] theorem tail_apply (M : Matrix (Fin (m + 1)) (Fin (m + 1)) S) (i j : Fin m) :
    tail M i j = M i.succ j.succ :=
  rfl

theorem tail_one : tail (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) S) = 1 := by
  ext i j
  simp [tail, Matrix.one_apply, Fin.succ_inj]

/-- The block of a product is the product of the blocks when the first matrix has vanishing
first column below the diagonal. -/
theorem tail_mul (M N : Matrix (Fin (m + 1)) (Fin (m + 1)) S)
    (hM : ∀ i : Fin m, M i.succ 0 = 0) : tail (M * N) = tail M * tail N := by
  ext i j
  simp [tail, Matrix.mul_apply, Fin.sum_univ_succ, hM]

theorem tail_map {S' : Type*} [CommRing S'] (f : S →+* S')
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) S) : tail (M.map f) = (tail M).map f :=
  rfl

variable (S m) in
/-- The first standard basis vector of `S^(m+1)`. -/
def firstBasisVector : Fin (m + 1) → S :=
  Pi.single 0 1

variable (S m) in
/-- The invertible matrices fixing the first standard basis vector. -/
def fixesFirstSubgroup : Subgroup (GL (Fin (m + 1)) S) where
  carrier := {g | g.val *ᵥ firstBasisVector S m = firstBasisVector S m}
  one_mem' := Matrix.one_mulVec _
  mul_mem' {g h} hg hh := by
    change (g * h).val *ᵥ firstBasisVector S m = firstBasisVector S m
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [Set.mem_ofPred_eq] at hg hh
    rw [hh, hg]
  inv_mem' {g} hg := by
    change (g⁻¹).val *ᵥ firstBasisVector S m = firstBasisVector S m
    rw [Set.mem_ofPred_eq] at hg
    conv_lhs => rw [← hg]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem mem_fixesFirstSubgroup_apply {g : GL (Fin (m + 1)) S}
    (hg : g ∈ fixesFirstSubgroup S m) (i : Fin (m + 1)) :
    g.val i 0 = firstBasisVector S m i := by
  have := congrFun hg i
  simpa [firstBasisVector, Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem mem_fixesFirstSubgroup_succ {g : GL (Fin (m + 1)) S}
    (hg : g ∈ fixesFirstSubgroup S m) (i : Fin m) :
    g.val i.succ 0 = 0 := by
  rw [mem_fixesFirstSubgroup_apply hg]
  exact Pi.single_eq_of_ne (Fin.succ_ne_zero i) 1

theorem mem_fixesFirstSubgroup_zero {g : GL (Fin (m + 1)) S}
    (hg : g ∈ fixesFirstSubgroup S m) :
    g.val 0 0 = 1 := by
  rw [mem_fixesFirstSubgroup_apply hg]
  exact Pi.single_eq_same 0 1

variable (S m) in
/-- The lower-right block as a homomorphism on matrices fixing the first basis vector. -/
def tailHom : fixesFirstSubgroup S m →* GL (Fin m) S where
  toFun g :=
    { val := tail g.1.val
      inv := tail (g.1⁻¹).val
      val_inv := by
        rw [← tail_mul _ _ fun i => mem_fixesFirstSubgroup_succ g.2 i, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, tail_one]
      inv_val := by
        rw [← tail_mul _ _ fun i => mem_fixesFirstSubgroup_succ (inv_mem g.2) i,
          ← Units.val_mul, inv_mul_cancel, Units.val_one, tail_one] }
  map_one' := by
    ext i j
    simp [tail, Matrix.one_apply, Fin.succ_inj]
  map_mul' g h := by
    apply Units.ext
    change tail (g.1 * h.1).val = tail g.1.val * tail h.1.val
    rw [Units.val_mul, tail_mul _ _ fun i => mem_fixesFirstSubgroup_succ g.2 i]

@[simp] theorem tailHom_apply_val (g : fixesFirstSubgroup S m) :
    (tailHom S m g).val = tail g.1.val :=
  rfl

/-- The kernel of the block homomorphism is commutative: its elements are the matrices
`[[1, a], [0, 1]]`. -/
theorem tailHom_ker_comm (g h : (tailHom S m).ker) : g * h = h * g := by
  have tail_eq : ∀ x : (tailHom S m).ker, ∀ i j : Fin m,
      x.1.1.val i.succ j.succ = if i = j then 1 else 0 := by
    intro x i j
    have := congrArg (fun y : GL (Fin m) S => y.val i j) ((MonoidHom.mem_ker).1 x.2)
    simpa [Matrix.one_apply] using this
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  change (g.1.1.val * h.1.1.val) i j = (h.1.1.val * g.1.1.val) i j
  have hg0 := mem_fixesFirstSubgroup_succ g.1.2
  have hh0 := mem_fixesFirstSubgroup_succ h.1.2
  have hg00 := mem_fixesFirstSubgroup_zero g.1.2
  have hh00 := mem_fixesFirstSubgroup_zero h.1.2
  have hgt := tail_eq g
  have hht := tail_eq h
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, hg0, hh0, hg00, hh00, hgt, hht, add_comm]

theorem firstBasisVector_ne_zero [Nontrivial S] : firstBasisVector S m ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [firstBasisVector] at this

theorem map_firstBasisVector {S' : Type*} [CommRing S'] (f : S →+* S') :
    (fun i => f (firstBasisVector S m i)) = firstBasisVector S' m := by
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [firstBasisVector]
  · simp [firstBasisVector, hi]

/-- Over a field, an invertible matrix moves any nonzero vector to the first basis vector. -/
theorem exists_mulVec_eq_firstBasisVector {K : Type*} [Field K] {v : Fin (m + 1) → K}
    (hv : v ≠ 0) : ∃ g : GL (Fin (m + 1)) K, g.val *ᵥ v = firstBasisVector K m := by
  let f := (LinearEquiv.toSpanNonzeroSingleton K _ v hv).symm ≪≫ₗ
    LinearEquiv.toSpanNonzeroSingleton K _ _ (firstBasisVector_ne_zero (S := K) (m := m))
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv g), ?_⟩
  have h1 := hg ⟨v, Submodule.mem_span_singleton_self v⟩
  have h2 : f ⟨v, Submodule.mem_span_singleton_self v⟩ =
      ⟨firstBasisVector K m, Submodule.mem_span_singleton_self _⟩ := by
    simp only [f, LinearEquiv.trans_apply]
    rw [← LinearEquiv.toSpanNonzeroSingleton_one K _ v hv, LinearEquiv.symm_apply_apply,
      LinearEquiv.toSpanNonzeroSingleton_one]
  rw [h2] at h1
  have h3 := Matrix.GeneralLinearGroup.toLin_apply
    (Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv g)) v
  rw [MulEquiv.apply_symm_apply] at h3
  rw [← Matrix.mulVecLin_apply, ← h3]
  exact h1.symm

end Tail

/-! ### The lower-right block of a representation fixing the first basis vector -/

section TailRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {m : ℕ}

theorem pointMatrix_mem_fixesFirstSubgroup (ρ : MatrixRepresentation G (Fin (m + 1)))
    (hρ : ρ.IsFixedVector (firstBasisVector R m)) (T : Over (Spec R)) (x : T ⟶ G.X) :
    ρ.pointMatrix T x ∈ fixesFirstSubgroup Γ(T.left, ⊤) m := by
  have h := hρ T x
  rw [map_firstBasisVector (scalarMap T)] at h
  exact h

/-- The matrices of a representation fixing the first basis vector, as a homomorphism into the
stabilizer of that vector. -/
def fixingPointMatrix (ρ : MatrixRepresentation G (Fin (m + 1)))
    (hρ : ρ.IsFixedVector (firstBasisVector R m)) (T : Over (Spec R)) :
    (T ⟶ G.X) →* fixesFirstSubgroup Γ(T.left, ⊤) m :=
  (ρ.pointMatrix T).codRestrict _ (pointMatrix_mem_fixesFirstSubgroup ρ hρ T)

/-- The lower-right blocks of the matrices of a representation fixing the first basis vector. -/
def tailPointMatrix (ρ : MatrixRepresentation G (Fin (m + 1)))
    (hρ : ρ.IsFixedVector (firstBasisVector R m)) (T : Over (Spec R)) :
    (T ⟶ G.X) →* GL (Fin m) Γ(T.left, ⊤) :=
  (tailHom Γ(T.left, ⊤) m).comp (fixingPointMatrix ρ hρ T)

theorem tailPointMatrix_naturality (ρ : MatrixRepresentation G (Fin (m + 1)))
    (hρ : ρ.IsFixedVector (firstBasisVector R m)) {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    tailPointMatrix ρ hρ T' (a ≫ x) =
      Matrix.GeneralLinearGroup.map a.left.appTop.hom (tailPointMatrix ρ hρ T x) := by
  apply Units.ext
  change tail (ρ.pointMatrix T' (a ≫ x)).val = (tail (ρ.pointMatrix T x).val).map _
  rw [pointMatrix_naturality, ← tail_map]
  rfl

theorem tailPoints_naturality (ρ : MatrixRepresentation G (Fin (m + 1)))
    (hρ : ρ.IsFixedVector (firstBasisVector R m)) {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    (GeneralLinear.pointsEquiv (Fin m) R T').symm (tailPointMatrix ρ hρ T' (a ≫ x)) =
      a ≫ (GeneralLinear.pointsEquiv (Fin m) R T).symm (tailPointMatrix ρ hρ T x) := by
  apply (GeneralLinear.pointsEquiv (Fin m) R _).injective
  rw [MulEquiv.apply_symm_apply, GeneralLinear.pointsEquiv_naturality,
    MulEquiv.apply_symm_apply, tailPointMatrix_naturality]

/-- The lower-right block of a representation fixing the first basis vector, as a
representation of the same group scheme. -/
def tailRepresentation (ρ : MatrixRepresentation G (Fin (m + 1)))
    (hρ : ρ.IsFixedVector (firstBasisVector R m)) : MatrixRepresentation G (Fin m) :=
  homOfPoints
    (fun T => (GeneralLinear.pointsEquiv (Fin m) R T).symm.toMonoidHom.comp
      (tailPointMatrix ρ hρ T))
    (fun a x => tailPoints_naturality ρ hρ a x)

theorem tailRepresentation_pointMatrix (ρ : MatrixRepresentation G (Fin (m + 1)))
    (hρ : ρ.IsFixedVector (firstBasisVector R m)) (T : Over (Spec R)) (x : T ⟶ G.X) :
    (tailRepresentation ρ hρ).pointMatrix T x = tailPointMatrix ρ hρ T x := by
  change GeneralLinear.pointsEquiv (Fin m) R T (x ≫ (tailRepresentation ρ hρ).hom.hom) = _
  rw [show x ≫ (tailRepresentation ρ hρ).hom.hom = _ from
    comp_homOfPoints _ (fun a x => tailPoints_naturality ρ hρ a x) T x]
  exact MulEquiv.apply_symm_apply _ _

end TailRepresentation

/-! ### Changing the basis by an invertible matrix over the base ring -/

section BasePoint

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {n : Type} [Fintype n] [DecidableEq n]

/-- The `R`-point of `GL_n` given by an invertible matrix with entries in `R`. -/
def basePoint (g : GL n R) :
    Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X :=
  (GeneralLinear.pointsEquiv n R (Over.mk (𝟙 (Spec R)))).symm
    (Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso R).inv.hom g)

theorem pointsEquiv_constantPoint_basePoint (g : GL n R) (T : Over (Spec R)) :
    GeneralLinear.pointsEquiv n R T
        ((GeneralLinear.groupScheme n R).constantPoint (basePoint g) T) =
      Matrix.GeneralLinearGroup.map (scalarMap T) g := by
  rw [GeneralLinear.pointsEquiv_constantPoint, basePoint, MulEquiv.apply_symm_apply]
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply, scalarMap]

/-- Changing the basis by `g` moves a fixed vector `v` to the fixed vector `g v`. -/
theorem isFixedVector_conjugate {ρ : MatrixRepresentation G n} {v : n → R}
    (hv : ρ.IsFixedVector v) (g : GL n R) :
    (ρ.conjugate (basePoint g)).IsFixedVector (g.val *ᵥ v) := by
  intro T x
  rw [conjugate_pointMatrix, pointsEquiv_constantPoint_basePoint]
  set A := Matrix.GeneralLinearGroup.map (scalarMap T) g
  have hmap : (fun i => scalarMap T ((g.val *ᵥ v) i)) =
      A.val *ᵥ fun i => scalarMap T (v i) := by
    funext i
    rw [RingHom.map_mulVec]
    rfl
  rw [hmap]
  simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_mulVec (M := (A⁻¹).val) (N := A.val), ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mulVec, hv T x]

theorem conjugate_pointMatrix_eq_one_iff (ρ : MatrixRepresentation G n)
    (g : Over.mk (𝟙 (Spec R)) ⟶ (GeneralLinear.groupScheme n R).X) (T : Over (Spec R))
    (x : T ⟶ G.X) : (ρ.conjugate g).pointMatrix T x = 1 ↔ ρ.pointMatrix T x = 1 := by
  rw [conjugate_pointMatrix, conj_eq_one_iff]

end BasePoint

/-! ### Kolchin's theorem on points -/

section Kolchin

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- For a unipotent group scheme over a field, some term of the derived series of every group
of points acts trivially in every finite-dimensional representation. -/
theorem exists_derivedSeries_le_ker (hG : IsUnipotent G) (m : ℕ) :
    ∀ (ρ : MatrixRepresentation G (Fin m)) (T : Over (Spec (CommRingCat.of k))),
      ∃ N, derivedSeries (T ⟶ G.X) N ≤ (ρ.pointMatrix T).ker := by
  induction m with
  | zero =>
    intro ρ T
    refine ⟨0, fun x _ => ?_⟩
    rw [MonoidHom.mem_ker]
    exact Units.ext (Matrix.ext fun i => Fin.elim0 i)
  | succ m ih =>
    intro ρ T
    obtain ⟨v, hv0, hv⟩ := hG (Fin (m + 1)) ρ
    obtain ⟨g, hg⟩ := exists_mulVec_eq_firstBasisVector hv0
    have hfix : (ρ.conjugate (basePoint g)).IsFixedVector (firstBasisVector k m) :=
      hg ▸ isFixedVector_conjugate hv g
    obtain ⟨N, hN⟩ := ih (tailRepresentation _ hfix) T
    refine ⟨N + 1, ?_⟩
    rw [derivedSeries_succ, Subgroup.commutator_le]
    intro x hx y hy
    have key : ∀ z ∈ derivedSeries (T ⟶ G.X) N,
        fixingPointMatrix _ hfix T z ∈ (tailHom Γ(T.left, ⊤) m).ker := fun z hz => by
      have h := hN hz
      rw [MonoidHom.mem_ker, tailRepresentation_pointMatrix] at h
      exact h
    have hc := congrArg Subtype.val (tailHom_ker_comm ⟨_, key x hx⟩ ⟨_, key y hy⟩)
    rw [MonoidHom.mem_ker, ← conjugate_pointMatrix_eq_one_iff ρ (basePoint g)]
    change ((fixingPointMatrix _ hfix T _ : fixesFirstSubgroup Γ(T.left, ⊤) m) :
      GL (Fin (m + 1)) Γ(T.left, ⊤)) = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm.2 hc]
    rfl

/-- The group of points of a unipotent group scheme admitting a faithful finite-dimensional
representation is solvable. -/
theorem isSolvable_points_of_mono (hG : IsUnipotent G) {m : ℕ}
    (ρ : MatrixRepresentation G (Fin m)) [Mono ρ.hom.hom] (T : Over (Spec (CommRingCat.of k))) :
    Group.IsSolvable (T ⟶ G.X) := by
  obtain ⟨N, hN⟩ := exists_derivedSeries_le_ker hG m ρ T
  refine ⟨⟨N, ?_⟩⟩
  rw [eq_bot_iff]
  refine le_trans hN ?_
  rw [(MonoidHom.ker_eq_bot_iff _).2 (pointMatrix_injective ρ T)]

end Kolchin

end MatrixRepresentation

open MatrixRepresentation in
/-- Kolchin's theorem on points: every group of points of an affine unipotent group scheme of
finite type over a field is solvable. -/
theorem isSolvable_points_of_isUnipotent {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsUnipotent G) (T : Over (Spec (CommRingCat.of k))) :
    Group.IsSolvable (T ⟶ G.X) := by
  obtain ⟨N, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have : IsClosedImmersion ρ.hom.hom.left := hρ
  have : Mono ρ.hom.hom := Over.mono_of_mono_left _
  exact isSolvable_points_of_mono hG ρ T

end Langlands.GroupScheme
