import Langlands.GroupScheme.RelativeUnipotent.CoordinateFiltrationTerm
import Langlands.GroupScheme.Reductive.LocalSplitHeightSubgroup

/-! # Represented root-height filtration terms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme.RelativeUnipotent

open LocalSplitCell Langlands.GroupTheory

variable {R : Type u} [CommRing R]
    {U : GroupScheme (Spec (CommRingCat.of R))}

/-- Scheme coordinates by additive root maps with positive heights and the
standard height-sum commutator bound, on every scheme test. -/
structure RootHeightChart (U : GroupScheme (Spec (CommRingCat.of R))) where
  dimension : ℕ
  roots : ULift.{u} (Fin dimension) → (Ga R ⟶ U)
  height : Fin dimension → ℕ
  height_pos : ∀ k, 0 < height k
  chart : (VectorGroup.groupScheme (CommRingCat.of R) dimension).X ≅ U.X
  formula : ∀ (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ (VectorGroup.groupScheme (CommRingCat.of R) dimension).X),
    x ≫ chart.hom = orderedProduct roots ULift.up T
      (VectorGroup.coordinates (CommRingCat.of R) dimension T x).toAdd
  commutator : ∀ (T : Over (Spec (CommRingCat.of R))) (k l : Fin dimension),
    ⁅rootFactor roots ULift.up T k, rootFactor roots ULift.up T l⁆ ≤
      HeightFiltration.level (rootFactor roots ULift.up T) height (height k + height l)

namespace RootHeightChart

variable (C : RootHeightChart U)

/-- Read the ordered root coordinates of a point. -/
def coordinates (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ U.X) :
    Fin C.dimension → Γ(T.left, ⊤) :=
  (VectorGroup.coordinates (CommRingCat.of R) C.dimension T (x ≫ C.chart.inv)).toAdd

@[simp]
theorem coordinates_orderedProduct (T : Over (Spec (CommRingCat.of R)))
    (c : Fin C.dimension → Γ(T.left, ⊤)) :
    C.coordinates T (orderedProduct C.roots ULift.up T c) = c := by
  let x := (VectorGroup.coordinates (CommRingCat.of R) C.dimension T).symm
    (Multiplicative.ofAdd c)
  have hx : x ≫ C.chart.hom = orderedProduct C.roots ULift.up T c := by
    simpa only [x, MulEquiv.apply_symm_apply, toAdd_ofAdd] using C.formula T x
  rw [← hx]
  simp only [coordinates, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    x, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem orderedProduct_coordinates (T : Over (Spec (CommRingCat.of R)))
    (x : T ⟶ U.X) :
    orderedProduct C.roots ULift.up T (C.coordinates T x) = x := by
  simpa only [coordinates, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    (C.formula T (x ≫ C.chart.inv)).symm

/-- The generated subgroup functor at height `d`. -/
abbrev subgroup (d : ℕ) : SubgroupFunctor U :=
  heightSubgroup C.roots ULift.up C.height d

/-- Collection and the scheme chart identify every height subgroup with exactly
the coordinate vectors supported in heights at least `d`. -/
theorem mem_subgroup_iff (T : Over (Spec (CommRingCat.of R))) (d : ℕ)
    (x : T ⟶ U.X) :
    x ∈ (C.subgroup d).carrier T ↔
      ∀ k, C.height k < d → C.coordinates T x k = 0 := by
  constructor
  · intro hx
    obtain ⟨c, hc, hlow, hprod⟩ := HeightFiltration.exists_coords
      (rootFactor C.roots ULift.up T) C.height C.height_pos (C.commutator T) d hx
    choose a ha using hc
    let b : Fin C.dimension → Γ(T.left, ⊤) :=
      fun k => if C.height k < d then 0 else (a k).toAdd
    have hb : orderedProduct C.roots ULift.up T b = x := by
      have hcoord (k : Fin C.dimension) :
          rootPoint (C.roots (ULift.up k)) T (b k) = c k := by
        dsimp only [b]
        split_ifs with hk
        · rw [rootPoint_zero, hlow k hk]
        · exact ha k
      change (List.ofFn fun k => rootPoint (C.roots (ULift.up k)) T (b k)).prod = x
      simp_rw [hcoord]
      exact hprod
    rw [← hb, coordinates_orderedProduct]
    exact fun k hk => ite_eq_left hk
  · intro hx
    rw [← C.orderedProduct_coordinates T x]
    apply (HeightFiltration.level (rootFactor C.roots ULift.up T) C.height d).list_prod_mem
    intro a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    rcases lt_or_ge (C.height k) d with hk | hk
    · rw [hx k hk, rootPoint_zero]
      exact one_mem _
    · exact HeightFiltration.le_level _ _ hk
        (mem_rootFactor C.roots ULift.up T k _)

/-- The finite coordinate block underlying one height term. -/
def support (d : ℕ) : Set (Fin C.dimension) := {k | d ≤ C.height k}

/-- A fixed finite enumeration of the coordinates in one height term. -/
def enumeration (d : ℕ) : Fin (Nat.card (C.support d)) ≃ C.support d :=
  (Finite.equivFin (C.support d)).symm

theorem mem_subgroup_iff_supported (T : Over (Spec (CommRingCat.of R)))
    (d : ℕ) (x : T ⟶ U.X) :
    x ∈ (C.subgroup d).carrier T ↔
      ∀ k, k ∉ C.support d →
        (VectorGroup.coordinates (CommRingCat.of R) C.dimension T
          (x ≫ C.chart.inv)).toAdd k = 0 := by
  rw [mem_subgroup_iff]
  simp only [support, Set.mem_ofPred_eq, not_le, coordinates]

/-- The actual smooth affine subgroup scheme representing a height term. Its
underlying scheme is the corresponding coordinate affine space. -/
abbrev groupScheme (d : ℕ) : GroupScheme (Spec (CommRingCat.of R)) :=
  CoordinateFiltrationTerm.groupScheme C.chart (C.support d) (C.enumeration d)
    (C.subgroup d) (fun T x => C.mem_subgroup_iff_supported T d x)

/-- The closed inclusion of one represented height term in the original group. -/
def inclusion (d : ℕ) : C.groupScheme d ⟶ U :=
  CoordinateFiltrationTerm.inclusion C.chart (C.support d) (C.enumeration d)
    (C.subgroup d) (fun T x => C.mem_subgroup_iff_supported T d x)

theorem isRepresentedBy_inclusion (d : ℕ) :
    (C.subgroup d).IsRepresentedBy (C.inclusion d) :=
  CoordinateFiltrationTerm.isRepresentedBy_inclusion _ _ _ _ _

theorem isClosedSubgroup_inclusion (d : ℕ) : IsClosedSubgroup (C.inclusion d) :=
  CoordinateFiltrationTerm.isClosedSubgroup_inclusion _ _ _ _ _

theorem smooth_groupScheme (d : ℕ) : Smooth (C.groupScheme d).X.hom :=
  CoordinateFiltrationTerm.smooth_groupScheme _ _ _ _ _

theorem isAffineHom_groupScheme (d : ℕ) : IsAffineHom (C.groupScheme d).X.hom :=
  CoordinateFiltrationTerm.isAffineHom_groupScheme _ _ _ _ _

/-- Height one is the full group on every test scheme. -/
theorem subgroup_one : C.subgroup 1 = ⊤ := by
  apply SubgroupFunctor.ext
  intro T
  apply top_unique
  intro x _
  exact (C.mem_subgroup_iff T 1 x).2 (fun k hk => False.elim (by
    have := C.height_pos k
    omega))

/-- Every height subgroup is normal in the original group. -/
theorem isNormal_subgroup (d : ℕ) : (C.subgroup d).IsNormal := by
  intro T g x _ hx
  have hg : g ∈ ⨆ k, rootFactor C.roots ULift.up T k := by
    have hg' : g ∈ (C.subgroup 1).carrier T := by
      rw [C.subgroup_one]
      exact Subgroup.mem_top _
    simpa only [subgroup, heightSubgroup, HeightFiltration.level_one _ _ C.height_pos]
      using hg'
  have hle : (⨆ k, rootFactor C.roots ULift.up T k) ≤
      Subgroup.normalizer (HeightFiltration.level
        (rootFactor C.roots ULift.up T) C.height d : Set (T ⟶ U.X)) :=
    iSup_le fun k => HeightFiltration.le_normalizer_level
      (rootFactor C.roots ULift.up T) C.height (C.commutator T) d k
  exact (Subgroup.le_normalizer_iff.mp hle) g hg x hx

/-- Once the height exceeds every root height, the represented subgroup has
only the identity point on every scheme test. -/
theorem subgroup_eq_bot {d : ℕ} (hd : ∀ k, C.height k < d) : C.subgroup d = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  exact HeightFiltration.level_eq_bot _ _ hd

end RootHeightChart

end Langlands.GroupScheme.RelativeUnipotent
