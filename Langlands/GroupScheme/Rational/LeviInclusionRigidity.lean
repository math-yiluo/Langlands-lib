import Langlands.GroupScheme.Rational.LeviRetraction

/-! # Rigidity of nested rational Levi subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {L M U V P : GroupScheme S}
  (l : L ⟶ P) (m : M ⟶ P) (r : U ⟶ P) (s : V ⟶ P)
  [IsIso (subgroupMultiplication l r)] [IsIso (subgroupMultiplication m s)]

/-- Two actual multiplication decompositions with nested first and second
factors have the same first-factor image on every test scheme. -/
theorem range_eq_of_nested_multiplication
    (hlm : SubgroupFunctor.range l ≤ SubgroupFunctor.range m)
    (hrs : SubgroupFunctor.range r ≤ SubgroupFunctor.range s) :
    SubgroupFunctor.range l = SubgroupFunctor.range m := by
  apply le_antisymm hlm
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  let a := leviComponent l r (y ≫ m.hom.hom)
  let n := radicalComponent l r (y ≫ m.hom.hom)
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp
    (hlm T (show a ≫ l.hom.hom ∈ (SubgroupFunctor.range l).carrier T from
      SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩))
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp
    (hrs T (show n ≫ r.hom.hom ∈ (SubgroupFunctor.range r).carrier T from
      SubgroupFunctor.mem_range.mpr ⟨n, rfl⟩))
  have hdecomp :
      (z ≫ m.hom.hom) * (w ≫ s.hom.hom) = y ≫ m.hom.hom := by
    rw [hz, hw]
    exact leviComponent_mul_radicalComponent l r _
  have hzy : z = y := by
    calc
      z = leviComponent m s ((z ≫ m.hom.hom) * (w ≫ s.hom.hom)) :=
        (leviComponent_product m s z w).symm
      _ = leviComponent m s (y ≫ m.hom.hom) := congrArg (leviComponent m s) hdecomp
      _ = y := leviComponent_comp_levi m s y
  exact SubgroupFunctor.mem_range.mpr ⟨a, hz.symm.trans (congrArg
    (fun t => t ≫ m.hom.hom) hzy)⟩

end Base

section Field

variable {k : Type u} [Field k]
  {L M P : GroupScheme (Spec (CommRingCat.of k))}
  {l : L ⟶ P} {m : M ⟶ P}

namespace IsRationalLeviSubgroup

/-- Nested rational Levi subgroups of the same group have equal all-test images. -/
theorem range_eq_of_le (hl : IsRationalLeviSubgroup l)
    (hm : IsRationalLeviSubgroup m)
    (hle : SubgroupFunctor.range l ≤ SubgroupFunctor.range m) :
    SubgroupFunctor.range l = SubgroupFunctor.range m := by
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  obtain ⟨V, s, hs, hmul'⟩ := hm.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l r) := hmul
  let : IsIso (subgroupMultiplication m s) := hmul'
  exact range_eq_of_nested_multiplication l m r s hle (hr.1.range_eq hs.1).le

/-- The canonical inclusion-compatible source isomorphism of nested rational
Levi subgroups, obtained from equality of their represented all-test images. -/
def isoOfRangeLe (hl : IsRationalLeviSubgroup l)
    (hm : IsRationalLeviSubgroup m)
    (hle : SubgroupFunctor.range l ≤ SubgroupFunctor.range m) : L ≅ M := by
  letI : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : IsClosedImmersion m.hom.hom.left := hm.isClosedSubgroup
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy
    (show (SubgroupFunctor.range l).IsRepresentedBy l from
      ⟨Over.mono_of_mono_left _, rfl⟩)
    (show (SubgroupFunctor.range l).IsRepresentedBy m from
      ⟨Over.mono_of_mono_left _, (hl.range_eq_of_le hm hle).symm⟩)

@[simp] theorem isoOfRangeLe_hom_comp (hl : IsRationalLeviSubgroup l)
    (hm : IsRationalLeviSubgroup m)
    (hle : SubgroupFunctor.range l ≤ SubgroupFunctor.range m) :
    (hl.isoOfRangeLe hm hle).hom ≫ m = l :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

@[simp] theorem isoOfRangeLe_inv_comp (hl : IsRationalLeviSubgroup l)
    (hm : IsRationalLeviSubgroup m)
    (hle : SubgroupFunctor.range l ≤ SubgroupFunctor.range m) :
    (hl.isoOfRangeLe hm hle).inv ≫ l = m := by
  calc
    (hl.isoOfRangeLe hm hle).inv ≫ l =
        (hl.isoOfRangeLe hm hle).inv ≫ ((hl.isoOfRangeLe hm hle).hom ≫ m) :=
      congrArg (fun f => (hl.isoOfRangeLe hm hle).inv ≫ f)
        (hl.isoOfRangeLe_hom_comp hm hle).symm
    _ = m := (hl.isoOfRangeLe hm hle).inv_hom_id_assoc m

/-- Compatibility with the inclusions uniquely determines the comparison map. -/
theorem isoOfRangeLe_hom_unique (hl : IsRationalLeviSubgroup l)
    (hm : IsRationalLeviSubgroup m)
    (hle : SubgroupFunctor.range l ≤ SubgroupFunctor.range m)
    {f : L ⟶ M} (hf : f ≫ m = l) :
    f = (hl.isoOfRangeLe hm hle).hom := by
  let : IsClosedImmersion m.hom.hom.left := hm.isClosedSubgroup
  have hrep : (SubgroupFunctor.range m).IsRepresentedBy m :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  apply hrep.hom_ext
  rw [hf, isoOfRangeLe_hom_comp]

end IsRationalLeviSubgroup

end Field

end Langlands.GroupScheme
