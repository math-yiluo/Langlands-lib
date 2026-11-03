import Langlands.GroupScheme.Rational.OrderedProductPoints
import Langlands.GroupScheme.Rational.RootProductStatement
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Ordered products through represented subgroup inclusions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor.IsRepresentedBy

variable {B : Scheme.{u}} {G U H : GroupScheme B}
    {F : SubgroupFunctor U} {V : SubgroupFunctor G}
    {j : H ⟶ U} {jU : U ⟶ G}

/-- A represented subgroup remains represented after a represented inclusion. -/
theorem comp (hj : F.IsRepresentedBy j) (hjU : V.IsRepresentedBy jU) :
    (F.map jU).IsRepresentedBy (j ≫ jU) := by
  let : Mono j.hom.hom := hj.1
  let : Mono jU.hom.hom := hjU.1
  refine ⟨?_, ?_⟩
  · change Mono (j.hom.hom ≫ jU.hom.hom)
    infer_instance
  · apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y ≫ j.hom.hom, by rw [← hj.2]; exact ⟨y, rfl⟩, ?_⟩
      change (y ≫ j.hom.hom) ≫ jU.hom.hom = x
      change y ≫ j.hom.hom ≫ jU.hom.hom = x at hy
      exact (Category.assoc y j.hom.hom jU.hom.hom).trans hy
    · rintro ⟨y, hy, hyx⟩
      rw [← hj.2] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨z, ?_⟩
      change z ≫ j.hom.hom ≫ jU.hom.hom = x
      change (z ≫ j.hom.hom) ≫ jU.hom.hom = x at hyx
      exact (Category.assoc z j.hom.hom jU.hom.hom).symm.trans hyx

end SubgroupFunctor.IsRepresentedBy

namespace RelativeRoot

variable {B : Scheme.{u}} {G U : GroupScheme B} {n : ℕ}
    {H : Fin n → GroupScheme B}

/-- Ordered multiplication commutes with postcomposition by a group homomorphism. -/
theorem orderedMultiplication_comp (j : ∀ r, H r ⟶ U) (f : U ⟶ G) :
    orderedMultiplication j ≫ f.hom.hom =
      orderedMultiplication (fun r => j r ≫ f) := by
  unfold orderedMultiplication
  change IsMonHom.monoidHom f.hom.hom _
    (List.ofFn fun r : Fin n => (Pi.π H r).hom.hom ≫ (j r).hom.hom).prod = _
  rw [map_list_prod, List.map_ofFn]
  rfl

/-- The canonical factors through a represented subgroup retain the exact ambient
ordered multiplication, including when the indexing set is empty. -/
theorem orderedMultiplication_factorHom {F : SubgroupFunctor G} {jU : U ⟶ G}
    (hjU : F.IsRepresentedBy jU) (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, SubgroupFunctor.range (j r) ≤ F) :
    orderedMultiplication (fun r => hjU.factorHom (j r) (hj r)) ≫ jU.hom.hom =
      orderedMultiplication j := by
  rw [orderedMultiplication_comp]
  congr 1
  funext r
  exact hjU.factorHom_comp _ _

/-- The actual internal ordered-product map, viewed as a scheme isomorphism when
it is an isomorphism. -/
def orderedProductIso {F : SubgroupFunctor G} {jU : U ⟶ G}
    (hjU : F.IsRepresentedBy jU) (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, SubgroupFunctor.range (j r) ≤ F)
    (hprod : IsIso (orderedMultiplication (fun r => hjU.factorHom (j r) (hj r)))) :
    (∏ᶜ H).X ≅ U.X :=
  let f : (∏ᶜ H).X ⟶ U.X :=
    orderedMultiplication (fun r => hjU.factorHom (j r) (hj r))
  let : IsIso f := hprod
  asIso f

/-- The constructed isomorphism has precisely the required ambient product map. -/
theorem orderedProductIso_hom_comp {F : SubgroupFunctor G} {jU : U ⟶ G}
    (hjU : F.IsRepresentedBy jU) (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, SubgroupFunctor.range (j r) ≤ F)
    (hprod : IsIso (orderedMultiplication (fun r => hjU.factorHom (j r) (hj r)))) :
    (orderedProductIso hjU j hj hprod).hom ≫ jU.hom.hom =
      orderedMultiplication j :=
  orderedMultiplication_factorHom hjU j hj

/-- An ordered product isomorphism inside a subgroup gives an isomorphism with the
required exact inclusion equation in the ambient group. -/
theorem exists_orderedProductIso {F : SubgroupFunctor G} {jU : U ⟶ G}
    (hjU : F.IsRepresentedBy jU) (j : ∀ r, H r ⟶ G)
    (hj : ∀ r, SubgroupFunctor.range (j r) ≤ F)
    (hprod : IsIso (orderedMultiplication (fun r => hjU.factorHom (j r) (hj r)))) :
    ∃ e : (∏ᶜ H).X ≅ U.X,
      e.hom ≫ jU.hom.hom = orderedMultiplication j :=
  ⟨orderedProductIso hjU j hj hprod, orderedProductIso_hom_comp hjU j hj hprod⟩

end RelativeRoot

end Langlands.GroupScheme
