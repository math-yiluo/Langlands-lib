import Langlands.GroupScheme.Derived.StructureStatement
import Langlands.GroupScheme.CorepresentedIntersection
import Langlands.GroupScheme.NormalizerRepresentability
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Closed representability of the scheme-theoretic derived subgroup

Over an affine base, the derived subgroup functor of an affine group scheme is the intersection
of the ranges of all closed commutator-containing subgroups. In chosen corepresented coordinates
`Spec B ≅ G`, each such range is cut out by an ideal of `B`, so the intersection is cut out by the
sum of these ideals and is represented by the corresponding closed subgroup scheme.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace DerivedRepresentability

variable {S : Scheme.{u}} {H G G' : GroupScheme S}

/-- Composing with an isomorphism of the ambient group transports ranges by preimage. -/
theorem mem_range_comp_iso_iff (i : H ⟶ G) (φ : G ≅ G') {T : Over S} (x : T ⟶ G.X) :
    x ≫ φ.hom.hom.hom ∈ (SubgroupFunctor.range (i ≫ φ.hom)).carrier T ↔
      x ∈ (SubgroupFunctor.range i).carrier T := by
  have eh : φ.hom.hom.hom ≫ φ.inv.hom.hom = 𝟙 G.X :=
    congrArg (fun f : G ⟶ G => f.hom.hom) φ.hom_inv_id
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have h := hy =≫ φ.inv.hom.hom
    change (y ≫ i.hom.hom ≫ φ.hom.hom.hom) ≫ φ.inv.hom.hom = x ≫ φ.hom.hom.hom ≫ φ.inv.hom.hom
      at h
    simpa only [Category.assoc, eh, Category.comp_id] using h
  · rintro ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    change y ≫ i.hom.hom ≫ φ.hom.hom.hom = (y ≫ i.hom.hom) ≫ φ.hom.hom.hom
    rw [Category.assoc]

/-- The admissible members of the intersection defining the derived subgroup: closed subgroups
whose range contains all commutators. -/
def Admissible (G : GroupScheme S) : Type (u + 1) :=
  { p : Σ H : GroupScheme S, H ⟶ G //
    IsClosedSubgroup p.2 ∧ (SubgroupFunctor.range p.2).ContainsCommutators }

/-- The derived subgroup is the pointwise intersection of the admissible ranges. -/
theorem derivedSubgroup_eq_intersection (G : GroupScheme S) :
    derivedSubgroup G =
      SubgroupFunctor.intersection fun a : Admissible G => SubgroupFunctor.range a.1.2 := by
  refine SubgroupFunctor.ext fun T => Subgroup.ext fun x => ?_
  rw [SubgroupFunctor.mem_intersection, mem_derivedSubgroup]
  exact ⟨fun hx a => hx a.1.1 a.1.2 a.2.1 a.2.2, fun hx H i hi hc => hx ⟨⟨H, i⟩, hi, hc⟩⟩

end DerivedRepresentability

open DerivedRepresentability in
/-- Every affine locally finite type group over a field has an actual affine locally finite type
closed subgroup representing its scheme-theoretic derived subgroup. -/
theorem derivedSubgroupRepresentability : DerivedSubgroupRepresentabilityStatement.{u} := by
  intro k _ G _ _
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let φ := AffineCoordinates.groupSchemeIso G
  let e := AffineCoordinates.corepresentation G
  let K : Admissible G → SubgroupFunctor
      (Corepresented.groupScheme (AffineCoordinates.functor G) e) :=
    fun a => SubgroupFunctor.range (a.1.2 ≫ φ.inv)
  have hex : ∀ a, ∃ I : Ideal (AffineCoordinates.algebra G),
      Corepresented.IsAffineCutOutBy e (K a) I := by
    intro a
    have : IsClosedImmersion (a.1.2 ≫ φ.inv).hom.hom.left := a.2.1.comp_iso φ.symm
    obtain ⟨I, hI⟩ := Corepresented.exists_ideal_range (a.1.2 ≫ φ.inv)
    exact ⟨I, Corepresented.isAffineCutOutBy_range hI⟩
  choose I hI using hex
  let d := Corepresented.intersectionHom hI ≫ φ.hom
  have hd : IsClosedSubgroup d := (Corepresented.isClosedSubgroup_intersectionHom hI).comp_iso φ
  have : IsClosedImmersion d.hom.hom.left := hd
  have hw : d.hom.hom.left ≫ G.X.hom = (Corepresented.intersectionScheme hI).X.hom :=
    Over.w d.hom.hom
  refine ⟨Corepresented.intersectionScheme hI, d, ?_, ?_, hd, ?_⟩
  · rw [← hw]
    infer_instance
  · rw [← hw]
    infer_instance
  · have hrep := ((Corepresented.isRepresentedBy_intersectionHom hI).comp_iso φ).2
    refine hrep.trans ?_
    rw [derivedSubgroup_eq_intersection]
    refine SubgroupFunctor.ext fun T => Subgroup.ext fun x => ?_
    rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_intersection,
      SubgroupFunctor.mem_intersection]
    exact forall_congr' fun a => mem_range_comp_iso_iff a.1.2 φ.symm x

end Langlands.GroupScheme
