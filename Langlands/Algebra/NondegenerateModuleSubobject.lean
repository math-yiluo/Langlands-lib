import Langlands.Algebra.NonUnitalModuleSubobject
import Langlands.Algebra.NondegenerateModuleExactnessProof

/-!
# Actual subobjects of nondegenerate original modules

Internal comparison for the setwise arguments in Renard I.6. The full
nondegenerate subcategory has the same subobjects as the ambient module
category, and these are the stable additive subgroups for the original action.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Algebra.NondegenerateModuleCat

universe uA uM

variable {A : Type uA} [NonUnitalRing A]

section Ambient

variable [(nondegenerateInclusion.{uA, uM} A).PreservesMonomorphisms]
variable (M : NondegenerateModuleCat.{uA, uM} A)

local instance mono_hom {N : NondegenerateModuleCat.{uA, uM} A}
    (f : N ⟶ M) [Mono f] : Mono f.hom :=
  (nondegenerateInclusion A).map_mono f

/-- Forget only the nondegeneracy certificate of a subobject arrow. -/
def subobjectToAmbient : Subobject M → Subobject M.obj :=
  Subobject.lift (fun {_} f _ => Subobject.mk f.hom) (by
    intro N P f g _ _ e w
    exact Subobject.mk_eq_mk_of_comm f.hom g.hom
      ((nondegenerateInclusion A).mapIso e)
      (congrArg (fun k : N ⟶ M => k.hom) w))

@[simp] theorem subobjectToAmbient_mk {N : NondegenerateModuleCat.{uA, uM} A}
    (f : N ⟶ M) [Mono f] :
    subobjectToAmbient M (Subobject.mk f) = Subobject.mk f.hom := rfl

/-- Factorization of original maps is unchanged in the full subcategory. -/
theorem subobjectToAmbient_le_iff (P Q : Subobject M) :
    subobjectToAmbient M P ≤ subobjectToAmbient M Q ↔ P ≤ Q := by
  induction P, Q using Subobject.ind₂ with
  | _ f g =>
    rw [subobjectToAmbient_mk, subobjectToAmbient_mk]
    constructor
    · intro h
      exact Subobject.mk_le_mk_of_comm
        (ObjectProperty.homMk (Subobject.ofMkLEMk f.hom g.hom h))
        (ObjectProperty.hom_ext _ (Subobject.ofMkLEMk_comp h))
    · intro h
      exact Subobject.mk_le_mk_of_comm (Subobject.ofMkLEMk f g h).hom
        (congrArg (fun k => k.hom) (Subobject.ofMkLEMk_comp h))

/-- Every ambient subobject has a nondegenerate original domain. -/
theorem subobjectToAmbient_surjective :
    Function.Surjective (subobjectToAmbient M) := by
  intro P
  let := NonUnitalModuleCat.nondegenerateProperty_isClosedUnderSubobjects.{uA, uM}
    (A := A)
  let N : NondegenerateModuleCat.{uA, uM} A :=
    ⟨(P : NonUnitalModuleCat.{uA, uM} A),
      (nondegenerateProperty A).prop_of_mono P.arrow M.property⟩
  let f : N ⟶ M := ObjectProperty.homMk P.arrow
  let : Mono f := (nondegenerateInclusion A).mono_of_mono_map
    (f := f) (inferInstance : Mono P.arrow)
  refine ⟨Subobject.mk f, ?_⟩
  rw [subobjectToAmbient_mk]
  exact Subobject.mk_arrow P

/-- The actual full inclusion induces an order isomorphism on subobjects. -/
def ambientSubobjectOrderIso : Subobject M ≃o Subobject M.obj :=
    { toFun := subobjectToAmbient M
      invFun := fun P => (subobjectToAmbient_surjective M P).choose
      left_inv := fun P => by
        apply le_antisymm
        · exact (subobjectToAmbient_le_iff M _ _).1
            (le_of_eq (subobjectToAmbient_surjective M _).choose_spec)
        · exact (subobjectToAmbient_le_iff M _ _).1
            (le_of_eq (subobjectToAmbient_surjective M _).choose_spec.symm)
      right_inv := fun P => (subobjectToAmbient_surjective M P).choose_spec
      map_rel_iff' := fun {_ _} => subobjectToAmbient_le_iff M _ _ }

end Ambient

/-- Subobjects in the actual nondegenerate category are precisely the
stable additive subgroups for the stored original action. -/
def subobjectOrderIso (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, uM} A) :
    Subobject M ≃o NonUnitalSubmodule A M.obj := by
  letI := abelian.{uA, uM} A hA
  letI := nondegenerateInclusion_preservesHomology.{uA, uM} hA
  exact (ambientSubobjectOrderIso M).trans (NonUnitalModuleCat.subobjectOrderIso M.obj)

section Laws

variable (hA : IsIdempotented A) {M : NondegenerateModuleCat.{uA, uM} A}

/-- The comparison sends a monomorphism to the range of its original map. -/
theorem mem_subobjectOrderIso_mk {N : NondegenerateModuleCat.{uA, uM} A}
    (f : N ⟶ M) [Mono f] (m : M.obj) :
    m ∈ subobjectOrderIso hA M (Subobject.mk f) ↔
      ∃ n : N.obj, f.hom.toAddMonoidHom n = m := by
  let := abelian.{uA, uM} A hA
  let := nondegenerateInclusion_preservesHomology.{uA, uM} hA
  let : Mono f.hom := (nondegenerateInclusion A).map_mono f
  change m ∈ NonUnitalModuleCat.subobjectOrderIso M.obj
    (subobjectToAmbient M (Subobject.mk f)) ↔ _
  rw [subobjectToAmbient_mk]
  exact NonUnitalModuleCat.mem_subobjectOrderIso_mk f.hom m

/-- Carrier equality with the range retains the original action and map. -/
theorem coe_subobjectOrderIso_mk {N : NondegenerateModuleCat.{uA, uM} A}
    (f : N ⟶ M) [Mono f] :
    (subobjectOrderIso hA M (Subobject.mk f) : Set M.obj) =
      Set.range f.hom.toAddMonoidHom :=
  Set.ext fun m => mem_subobjectOrderIso_mk hA f m

/-- Arbitrary categorical subobjects are represented by their actual arrows. -/
theorem mem_subobjectOrderIso (P : Subobject M) (m : M.obj) :
    m ∈ subobjectOrderIso hA M P ↔
      ∃ n : (P : NondegenerateModuleCat.{uA, uM} A).obj,
        P.arrow.hom.toAddMonoidHom n = m := by
  conv_lhs => rw [← Subobject.mk_arrow P]
  exact mem_subobjectOrderIso_mk hA P.arrow m

/-- Stable-subgroup inclusion both preserves and reflects categorical order. -/
theorem subobjectOrderIso_le_iff {P Q : Subobject M} :
    subobjectOrderIso hA M P ≤ subobjectOrderIso hA M Q ↔ P ≤ Q :=
  (subobjectOrderIso hA M).le_iff_le

include hA in
/-- Factorization of monomorphism classes is inclusion of their original ranges. -/
theorem subobject_mk_le_mk_iff {N₁ N₂ : NondegenerateModuleCat.{uA, uM} A}
    (f₁ : N₁ ⟶ M) (f₂ : N₂ ⟶ M) [Mono f₁] [Mono f₂] :
    Subobject.mk f₁ ≤ Subobject.mk f₂ ↔
      Set.range f₁.hom.toAddMonoidHom ⊆ Set.range f₂.hom.toAddMonoidHom := by
  rw [← subobjectOrderIso_le_iff hA, ← SetLike.coe_subset_coe,
    coe_subobjectOrderIso_mk, coe_subobjectOrderIso_mk]

include hA in
/-- An inclusion of original ranges is witnessed by an actual original intertwiner. -/
theorem exists_factor_iff_range_subset {N₁ N₂ : NondegenerateModuleCat.{uA, uM} A}
    (f₁ : N₁ ⟶ M) (f₂ : N₂ ⟶ M) [Mono f₁] [Mono f₂] :
    (∃ i : N₁ ⟶ N₂, i ≫ f₂ = f₁) ↔
      Set.range f₁.hom.toAddMonoidHom ⊆ Set.range f₂.hom.toAddMonoidHom := by
  rw [← subobject_mk_le_mk_iff hA f₁ f₂]
  exact ⟨fun ⟨i, hi⟩ => Subobject.mk_le_mk_of_comm i hi,
    fun h => ⟨Subobject.ofMkLEMk f₁ f₂ h, Subobject.ofMkLEMk_comp h⟩⟩

end Laws

section Subtype

variable (M : NondegenerateModuleCat.{uA, uM} A)

/-- The original stable subgroup as an object of the nondegenerate category. -/
def submoduleObject (S : NonUnitalSubmodule A M.obj) :
    NondegenerateModuleCat.{uA, uM} A := by
  letI := NonUnitalModuleCat.nondegenerateProperty_isClosedUnderSubobjects.{uA, uM}
    (A := A)
  exact ⟨NonUnitalModuleCat.of A S,
    (nondegenerateProperty A).prop_of_mono (NonUnitalModuleCat.subtypeHom S) M.property⟩

/-- The subtype inclusion with its unchanged original intertwiner. -/
def subtypeHom (S : NonUnitalSubmodule A M.obj) : submoduleObject M S ⟶ M :=
  ObjectProperty.homMk (NonUnitalModuleCat.subtypeHom S)

/-- The underlying original intertwiner is the existing stable-subgroup inclusion. -/
theorem subtypeHom_hom (S : NonUnitalSubmodule A M.obj) :
    (subtypeHom M S).hom = S.subtype := rfl

@[simp] theorem subtypeHom_apply (S : NonUnitalSubmodule A M.obj) (s : S) :
    (subtypeHom M S).hom.toAddMonoidHom s = s := rfl

instance mono_subtypeHom (S : NonUnitalSubmodule A M.obj) : Mono (subtypeHom M S) :=
  (nondegenerateInclusion A).mono_of_mono_map
    (f := subtypeHom M S) (NonUnitalModuleCat.mono_subtypeHom S)

variable (hA : IsIdempotented A)

/-- The subtype inclusion returns the very same stable subgroup. -/
@[simp] theorem subobjectOrderIso_mk_subtypeHom (S : NonUnitalSubmodule A M.obj) :
    subobjectOrderIso hA M (Subobject.mk (subtypeHom M S)) = S :=
  SetLike.ext fun m => (mem_subobjectOrderIso_mk hA (subtypeHom M S) m).trans
    ⟨fun ⟨n, hn⟩ => hn ▸ n.property, fun hm => ⟨⟨m, hm⟩, rfl⟩⟩

/-- The inverse comparison is represented by the original subtype inclusion. -/
@[simp] theorem subobjectOrderIso_symm_apply (S : NonUnitalSubmodule A M.obj) :
    (subobjectOrderIso hA M).symm S = Subobject.mk (subtypeHom M S) :=
  (subobjectOrderIso hA M).symm_apply_eq.2
    (subobjectOrderIso_mk_subtypeHom M hA S).symm

/-- Each categorical subobject equals the inclusion of its original range. -/
@[simp] theorem mk_subtypeHom_subobjectOrderIso (P : Subobject M) :
    Subobject.mk (subtypeHom M (subobjectOrderIso hA M P)) = P := by
  rw [← subobjectOrderIso_symm_apply M hA, OrderIso.symm_apply_apply]

include hA in
/-- The factorization order on subtype inclusions is subgroup inclusion. -/
theorem mk_subtypeHom_le_mk_subtypeHom_iff {S T : NonUnitalSubmodule A M.obj} :
    Subobject.mk (subtypeHom M S) ≤ Subobject.mk (subtypeHom M T) ↔ S ≤ T := by
  rw [← subobjectOrderIso_symm_apply M hA, ← subobjectOrderIso_symm_apply M hA,
    OrderIso.le_iff_le]

end Subtype

/-- The order comparison has independent coefficient and carrier universes. -/
example : (A : Type uA) → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{uA, uM} A) →
    Subobject M ≃o @NonUnitalSubmodule A M.obj _ M.obj.isAddCommGroup M.obj.isModule :=
  @subobjectOrderIso.{uA, uM}

example : (A : Type) → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{0, 1} A) →
    Subobject M ≃o NonUnitalSubmodule A M.obj := @subobjectOrderIso.{0, 1}

example : (A : Type 1) → [NonUnitalRing A] → (hA : IsIdempotented A) →
    (M : NondegenerateModuleCat.{1, 0} A) →
    Subobject M ≃o NonUnitalSubmodule A M.obj := @subobjectOrderIso.{1, 0}

/-! Complete intrinsic law interfaces retain both independent universes. -/

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N : NondegenerateModuleCat.{uA, uM} A} → (f : N ⟶ M) → [Mono f] →
    (m : M.obj) →
      (m ∈ subobjectOrderIso hA M (Subobject.mk f) ↔
        ∃ n : N.obj, f.hom.toAddMonoidHom n = m) :=
  @mem_subobjectOrderIso_mk.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    (M : NondegenerateModuleCat.{uA, uM} A) → (hA : IsIdempotented A) →
    (S : NonUnitalSubmodule A M.obj) →
      (subobjectOrderIso hA M).symm S = Subobject.mk (subtypeHom M S) :=
  @subobjectOrderIso_symm_apply.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] →
    (M : NondegenerateModuleCat.{uA, uM} A) → (hA : IsIdempotented A) →
    (P : Subobject M) →
      Subobject.mk (subtypeHom M (subobjectOrderIso hA M P)) = P :=
  @mk_subtypeHom_subobjectOrderIso.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M : NondegenerateModuleCat.{uA, uM} A} → {P Q : Subobject M} →
      (subobjectOrderIso hA M P ≤ subobjectOrderIso hA M Q ↔ P ≤ Q) :=
  @subobjectOrderIso_le_iff.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → (hA : IsIdempotented A) →
    {M N₁ N₂ : NondegenerateModuleCat.{uA, uM} A} →
    (f₁ : N₁ ⟶ M) → (f₂ : N₂ ⟶ M) → [Mono f₁] → [Mono f₂] →
      ((∃ i : N₁ ⟶ N₂, i ≫ f₂ = f₁) ↔
        Set.range f₁.hom.toAddMonoidHom ⊆ Set.range f₂.hom.toAddMonoidHom) :=
  @exists_factor_iff_range_subset.{uA, uM}

end Langlands.Algebra.NondegenerateModuleCat
