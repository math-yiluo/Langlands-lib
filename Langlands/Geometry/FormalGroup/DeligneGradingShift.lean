import Langlands.Geometry.FormalGroup.DeligneIsomorphism

/-! # Actual cyclic grading shifts of Deligne lattice and tangent sheaves -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

/-- Relabeling a family of submodules by a bijection preserves its actual internal sum. -/
theorem isInternal_reindex
    {R V ι κ : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [DecidableEq ι] [DecidableEq κ] (A : ι → Submodule R V)
    (hA : DirectSum.IsInternal A) (e : κ ≃ ι) :
    DirectSum.IsInternal (fun i => A (e i)) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact hA.submodule_iSupIndep.comp e.injective
  · exact e.iSup_comp.trans hA.submodule_iSup_eq_top

section Graded

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {d : ℕ} [NeZero d] {R : Sheaf J CommRingCat.{u}}
  {a : (R.obj ⋙ CategoryTheory.forget CommRingCat).sections}

namespace GradedPiSheaf

/-- The new degree i is the old degree i+k; the total sheaf and Pi operator are unchanged. -/
def shift (M : GradedPiSheaf d R a) (k : ZMod d) : GradedPiSheaf d R a where
  toPiSheaf := M.toPiSheaf
  component i := M.component (i + k)
  isInternal U := isInternal_reindex _ (M.isInternal U) (Equiv.addRight k)
  pi_mem U i x hx := by
    simpa only [add_right_comm i 1 k] using M.pi_mem U (i + k) x hx

/-- A genuine homogeneous morphism remains homogeneous for the shifted degrees. -/
def shiftMap {M N : GradedPiSheaf d R a} (f : M ⟶ N) (k : ZMod d) :
    M.shift k ⟶ N.shift k where
  val := f.val
  homogeneous U i x hx := f.homogeneous U (i + k) x hx

/-- Cyclic translation of degrees is functorial for actual operator-compatible sheaf maps. -/
def shiftFunctor (k : ZMod d) : GradedPiSheaf d R a ⥤ GradedPiSheaf d R a where
  obj M := M.shift k
  map f := shiftMap f k
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext rfl

variable (M : GradedPiSheaf d R a)

/-- A zero shift identifies actual graded objects by the identity on their total sheaf. -/
def shiftZeroIso : M.shift 0 ≅ M where
  hom := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      change x ∈ (M.component i).toSubmodule.obj U
      simpa only [shift, add_zero] using hx }
  inv := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      change x ∈ (M.component (i + 0)).toSubmodule.obj U
      simpa only [add_zero] using hx }
  hom_inv_id := Hom.ext (Category.id_comp _)
  inv_hom_id := Hom.ext (Category.id_comp _)

/-- The comparison of successive and summed shifts is an actual homogeneous isomorphism. -/
def shiftAddIso (k l : ZMod d) : (M.shift k).shift l ≅ M.shift (k + l) where
  hom := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      change x ∈ (M.component (i + (k + l))).toSubmodule.obj U
      simpa only [shift, add_assoc, add_comm, add_left_comm] using hx }
  inv := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      change x ∈ (M.component ((i + l) + k)).toSubmodule.obj U
      simpa only [shift, add_assoc, add_comm, add_left_comm] using hx }
  hom_inv_id := Hom.ext (Category.id_comp _)
  inv_hom_id := Hom.ext (Category.id_comp _)

/-- Shifts whose degrees add to zero cancel by identity maps on the total sheaf. -/
def shiftCancelIso (k l : ZMod d) (h : k + l = 0) : (M.shift k).shift l ≅ M where
  hom := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      have hi : (i + l) + k = i := by
        calc
          _ = i + (k + l) := by abel
          _ = i := by rw [h, add_zero]
      change x ∈ (M.component i).toSubmodule.obj U
      simpa only [shift, hi] using hx }
  inv := {
    val := 𝟙 M.toPiSheaf
    homogeneous U i x hx := by
      have hi : (i + l) + k = i := by
        calc
          _ = i + (k + l) := by abel
          _ = i := by rw [h, add_zero]
      change x ∈ (M.component ((i + l) + k)).toSubmodule.obj U
      simpa only [hi] using hx }
  hom_inv_id := Hom.ext (Category.id_comp _)
  inv_hom_id := Hom.ext (Category.id_comp _)

/-- Translation by -k undoes translation by k through genuine homogeneous maps. -/
def shiftNegIso (k : ZMod d) : (M.shift k).shift (-k) ≅ M :=
  M.shiftCancelIso k (-k) (add_neg_cancel k)

/-- The zero-shift comparison is natural in actual homogeneous morphisms. -/
def shiftZeroNatIso : shiftFunctor (d := d) (R := R) (a := a) 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => M.shiftZeroIso) (fun _f =>
    Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- Summing two shifts is a natural comparison of actual sheaf functors. -/
def shiftAddNatIso (k l : ZMod d) :
    shiftFunctor (R := R) (a := a) k ⋙ shiftFunctor l ≅ shiftFunctor (k + l) :=
  NatIso.ofComponents (fun M => M.shiftAddIso k l) (fun _f =>
    Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- Cancellation of opposite total degrees is natural. -/
def shiftCancelNatIso (k l : ZMod d) (h : k + l = 0) :
    shiftFunctor (R := R) (a := a) k ⋙ shiftFunctor l ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => M.shiftCancelIso k l h) (fun _f =>
    Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- Cyclic degree translation is an equivalence, inverse to the opposite translation. -/
def shiftEquivalence (k : ZMod d) : GradedPiSheaf d R a ≌ GradedPiSheaf d R a where
  functor := shiftFunctor k
  inverse := shiftFunctor (-k)
  unitIso := (shiftCancelNatIso k (-k) (add_neg_cancel k)).symm
  counitIso := shiftCancelNatIso (-k) k (neg_add_cancel k)
  functor_unitIso_comp _ := Hom.ext (Category.id_comp _)

/-- Equal component indices identify their actual inclusions. -/
theorem component_eqToHom_inclusion {i j : ZMod d} (h : i = j) :
    eqToHom (congrArg M.componentSheaf h) ≫ M.componentInclusion j =
      M.componentInclusion i := by
  subst j
  simp

/-- The actual inclusion of each homogeneous subsheaf is monic. -/
instance componentInclusion_mono (i : ZMod d) : Mono (M.componentInclusion i) :=
  inferInstanceAs (Mono (M.component i).ι)

/-- The shifted degree-one map is the old map, with its target index transported. -/
theorem shift_componentPi (k i : ZMod d) :
    (M.shift k).componentPi i ≫
        eqToHom (congrArg M.componentSheaf (add_right_comm i 1 k)) =
      M.componentPi (i + k) := by
  apply (cancel_mono (M.componentInclusion (i + k + 1))).mp
  rw [Category.assoc, M.component_eqToHom_inclusion (add_right_comm i 1 k),
    M.componentPi_inclusion]
  exact (M.shift k).componentPi_inclusion i

end GradedPiSheaf

end Graded

section Lattice

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O} {X : TopCat.{u}}

namespace LatticePiSheaf

/-- Cyclic translation retains the actual flat coefficient sheaf and relabels its summands. -/
def shift (M : LatticePiSheaf d π X) (k : ZMod d) : LatticePiSheaf d π X where
  sheaf := M.sheaf
  flat := M.flat
  component i := M.component (i + k)
  inclusion i := M.inclusion (i + k)
  injective i := M.injective (i + k)
  isInternal U := isInternal_reindex _ (M.isInternal U) (Equiv.addRight k)
  pi i := M.pi (i + k) ≫
    eqToHom (congrArg M.component (add_right_comm i k 1))
  pi_inclusion i := by
    have h (i j : ZMod d) (hij : i = j) :
        eqToHom (congrArg M.component hij) ≫ M.inclusion j = M.inclusion i := by
      subst j
      simp
    rw [Category.assoc, h _ _ (add_right_comm i k 1)]
    exact M.pi_inclusion (i + k)

/-- The same coefficient-linear map and relabeled component maps give a genuine shifted map. -/
def shiftMap {M N : LatticePiSheaf d π X} (f : M ⟶ N) (k : ZMod d) :
    M.shift k ⟶ N.shift k where
  total := f.total
  component i := f.component (i + k)
  inclusion i := f.inclusion (i + k)

/-- Grading shifts are functors on the actual flat lattice category. -/
def shiftFunctor (k : ZMod d) : LatticePiSheaf d π X ⥤ LatticePiSheaf d π X where
  obj M := M.shift k
  map f := shiftMap f k
  map_id _ := Hom.ext_total rfl
  map_comp _ _ := Hom.ext_total rfl

variable (M : LatticePiSheaf d π X)

omit [NeZero d] in
/-- The component identification obtained from equal degrees respects the actual inclusion. -/
theorem component_eqToHom_inclusion {i j : ZMod d} (h : i = j) :
    eqToHom (congrArg M.component h) ≫ M.inclusion j = M.inclusion i := by
  subst j
  simp

/-- A zero shift is canonically the original lattice with identity on the total sheaf. -/
def shiftZeroIso : M.shift 0 ≅ M where
  hom := {
    total := 𝟙 M.sheaf
    component i := eqToHom (congrArg M.component (add_zero i))
    inclusion i := by
      dsimp only [shift]
      exact (M.component_eqToHom_inclusion (add_zero i)).trans
        ((congrArg (fun t => M.inclusion (i + 0) ≫ t)
          ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
            (Category.comp_id _)).symm }
  inv := {
    total := 𝟙 M.sheaf
    component i := eqToHom (congrArg M.component (add_zero i).symm)
    inclusion i := by
      dsimp only [shift]
      exact (M.component_eqToHom_inclusion (add_zero i).symm).trans
        ((congrArg (fun t => M.inclusion i ≫ t)
          ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
            (Category.comp_id _)).symm }
  hom_inv_id := Hom.ext_total (Category.id_comp _)
  inv_hom_id := Hom.ext_total (Category.id_comp _)

/-- Successive shifts and the sum shift are identified by their actual component transports. -/
def shiftAddIso (k l : ZMod d) : (M.shift k).shift l ≅ M.shift (k + l) where
  hom := {
    total := 𝟙 M.sheaf
    component i := eqToHom (congrArg M.component
      (by abel : (i + l) + k = i + (k + l)))
    inclusion i := by
      dsimp only [shift]
      exact (M.component_eqToHom_inclusion (by abel)).trans
        ((congrArg (fun t => M.inclusion ((i + l) + k) ≫ t)
          ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
            (Category.comp_id _)).symm }
  inv := {
    total := 𝟙 M.sheaf
    component i := eqToHom (congrArg M.component
      (by abel : i + (k + l) = (i + l) + k))
    inclusion i := by
      dsimp only [shift]
      exact (M.component_eqToHom_inclusion (by abel)).trans
        ((congrArg (fun t => M.inclusion (i + (k + l)) ≫ t)
          ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
            (Category.comp_id _)).symm }
  hom_inv_id := Hom.ext_total (Category.id_comp _)
  inv_hom_id := Hom.ext_total (Category.id_comp _)

/-- Shifts whose degrees add to zero cancel on the actual lattice sheaf. -/
def shiftCancelIso (k l : ZMod d) (h : k + l = 0) : (M.shift k).shift l ≅ M := by
  have hi (i : ZMod d) : (i + l) + k = i := by
    calc
      _ = i + (k + l) := by abel
      _ = i := by rw [h, add_zero]
  exact {
    hom := {
      total := 𝟙 M.sheaf
      component i := eqToHom (congrArg M.component (hi i))
      inclusion i := by
        dsimp only [shift]
        exact (M.component_eqToHom_inclusion (hi i)).trans
          ((congrArg (fun t => M.inclusion ((i + l) + k) ≫ t)
            ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
              (Category.comp_id _)).symm }
    inv := {
      total := 𝟙 M.sheaf
      component i := eqToHom (congrArg M.component (hi i).symm)
      inclusion i := by
        dsimp only [shift]
        exact (M.component_eqToHom_inclusion (hi i).symm).trans
          ((congrArg (fun t => M.inclusion i ≫ t)
            ((latticeScalarFunctor d π X).map_id M.sheaf)).trans
              (Category.comp_id _)).symm }
    hom_inv_id := Hom.ext_total (Category.id_comp _)
    inv_hom_id := Hom.ext_total (Category.id_comp _) }

/-- The inverse degree translation gives a genuine inverse-map comparison. -/
def shiftNegIso (k : ZMod d) : (M.shift k).shift (-k) ≅ M :=
  M.shiftCancelIso k (-k) (add_neg_cancel k)

/-- The zero-shift comparison is natural for actual lattice morphisms. -/
def shiftZeroNatIso : shiftFunctor (d := d) (π := π) (X := X) 0 ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => M.shiftZeroIso) (fun _f =>
    Hom.ext_total ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- The comparison between successive shifts and their sum is natural. -/
def shiftAddNatIso (k l : ZMod d) :
    shiftFunctor (π := π) (X := X) k ⋙ shiftFunctor l ≅ shiftFunctor (k + l) :=
  NatIso.ofComponents (fun M => M.shiftAddIso k l) (fun _f =>
    Hom.ext_total ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- Cancellation of opposite total degrees is a natural lattice isomorphism. -/
def shiftCancelNatIso (k l : ZMod d) (h : k + l = 0) :
    shiftFunctor (π := π) (X := X) k ⋙ shiftFunctor l ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M => M.shiftCancelIso k l h) (fun _f =>
    Hom.ext_total ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- Shifting the actual graded lattice is an equivalence with inverse shift -k. -/
def shiftEquivalence (k : ZMod d) : LatticePiSheaf d π X ≌ LatticePiSheaf d π X where
  functor := shiftFunctor k
  inverse := shiftFunctor (-k)
  unitIso := (shiftCancelNatIso k (-k) (add_neg_cancel k)).symm
  counitIso := shiftCancelNatIso (-k) k (neg_add_cancel k)
  functor_unitIso_comp _ := Hom.ext_total (Category.id_comp _)

end LatticePiSheaf

end Lattice

section Lines

variable {d : ℕ} [NeZero d] {S : Scheme.{u}} {a : Γ(S, ⊤)}

namespace GradedPiSheaf

variable (M : GradedPiSheaf d S.sheaf (schemeScalar S a))

/-- Cyclic degree translation relabels the actual fibrewise Pi-zero loci. -/
theorem piZeroLocus_shift (k i : ZMod d) :
    (M.shift k).piZeroLocus i = M.piZeroLocus (i + k) := by
  ext x
  let F := Scheme.Modules.pullback (S.fromSpecResidueField x)
  let t := eqToHom (congrArg M.componentSheaf (add_right_comm i 1 k))
  have ht : IsIso (F.map t) := inferInstance
  have h := congrArg (fun f => F.map f) (M.shift_componentPi k i)
  change F.map ((M.shift k).componentPi i ≫ t) = F.map (M.componentPi (i + k)) at h
  rw [F.map_comp] at h
  change F.map ((M.shift k).componentPi i) = 0 ↔ F.map (M.componentPi (i + k)) = 0
  constructor
  · intro hx
    rw [← h, hx, Limits.zero_comp]
  · intro hx
    apply (cancel_mono (F.map t)).mp
    rw [Limits.zero_comp, h, hx]

end GradedPiSheaf

namespace LinePiSheaf

/-- Relabel the actual invertible tangent summands, retaining their total sheaf and operator. -/
def shift (M : LinePiSheaf d S a) (k : ZMod d) : LinePiSheaf d S a where
  graded := M.graded.shift k
  line i := M.line (i + k)

/-- The induced translation on genuine line-sheaf isomorphism classes. -/
def IsoClass.shift (k : ZMod d) : IsoClass (d := d) (S := S) (a := a) →
    IsoClass (d := d) (S := S) (a := a) :=
  Quotient.map (fun M => M.shift k) (fun _ _ ⟨e⟩ =>
    ⟨(GradedPiSheaf.shiftFunctor k).mapIso e⟩)

namespace IsoClass

variable (q : IsoClass (d := d) (S := S) (a := a))

/-- The zero translation acts identically on genuine line-sheaf classes. -/
@[simp]
theorem shift_zero : shift 0 q = q := by
  refine Quotient.inductionOn q ?_
  intro M
  exact Quotient.sound ⟨M.graded.shiftZeroIso⟩

/-- Successive translations of line-sheaf classes add their degrees. -/
theorem shift_add (k l : ZMod d) : shift l (shift k q) = shift (k + l) q := by
  refine Quotient.inductionOn q ?_
  intro M
  exact Quotient.sound ⟨M.graded.shiftAddIso k l⟩

/-- Degree translation is bijective on the actual line-sheaf isomorphism classes. -/
def shiftEquiv (k : ZMod d) :
    IsoClass (d := d) (S := S) (a := a) ≃ IsoClass (d := d) (S := S) (a := a) where
  toFun := shift k
  invFun := shift (-k)
  left_inv q := by rw [shift_add, add_neg_cancel, shift_zero]
  right_inv q := by rw [shift_add, neg_add_cancel, shift_zero]

end IsoClass

end LinePiSheaf

end Lines

end Langlands.DeligneFormalSpace
