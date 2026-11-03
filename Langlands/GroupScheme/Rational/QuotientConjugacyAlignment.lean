import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Lifting conjugacy witnesses and aligning maximal tori over a quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section ArbitraryBase

variable {S : Scheme.{u}} {G Q H H' : GroupScheme S}

/-- A section of the underlying scheme morphism lifts points on every test.
It need not be a homomorphism of group schemes. -/
theorem points_surjective_of_scheme_section (q : G ⟶ Q)
    (s : Q.X ⟶ G.X) (hs : s ≫ q.hom.hom = 𝟙 Q.X) (T : Over S) :
    Function.Surjective (fun g : T ⟶ G.X => g ≫ q.hom.hom) := by
  intro a
  refine ⟨a ≫ s, ?_⟩
  change (a ≫ s) ≫ q.hom.hom = a
  rw [Category.assoc, hs, Category.comp_id]

/-- Choose a rational conjugating point upstairs and retain the quotient
conjugacy's actual source isomorphism. This aligns the two quotient maps;
it does not assert conjugacy upstairs. -/
def conjugatingDataOverQuotient (q : G ⟶ Q)
    (hq : Function.Surjective
      (fun g : Over.mk (𝟙 S) ⟶ G.X => g ≫ q.hom.hom))
    {i : H ⟶ G} {i' : H' ⟶ G}
    (h : SubgroupConjugate (i ≫ q) (i' ≫ q)) :
    Σ (g : Over.mk (𝟙 S) ⟶ G.X),
      {e : H ≅ H' //
        (i ≫ (G.innerIso g).hom) ≫ q = e.hom ≫ (i' ≫ q)} := by
  let a := Classical.choose h
  let e := Classical.choose (Classical.choose_spec h)
  have ha : (i ≫ q) ≫ (Q.innerIso a).hom = e.hom ≫ (i' ≫ q) :=
    Classical.choose_spec (Classical.choose_spec h)
  let g := Classical.choose (hq a)
  have hg : g ≫ q.hom.hom = a := Classical.choose_spec (hq a)
  refine ⟨g, e, ?_⟩
  calc
    (i ≫ (G.innerIso g).hom) ≫ q =
        (i ≫ q) ≫ (Q.innerIso (g ≫ q.hom.hom)).hom := by
      rw [Category.assoc, innerIso_hom_comp, Category.assoc]
    _ = e.hom ≫ (i' ≫ q) := by rw [hg]; exact ha

/-- The chosen lift and source isomorphism satisfy the exact alignment equation. -/
theorem conjugatingDataOverQuotient_spec (q : G ⟶ Q)
    (hq : Function.Surjective
      (fun g : Over.mk (𝟙 S) ⟶ G.X => g ≫ q.hom.hom))
    {i : H ⟶ G} {i' : H' ⟶ G}
    (h : SubgroupConjugate (i ≫ q) (i' ≫ q)) :
    (i ≫ (G.innerIso (conjugatingDataOverQuotient q hq h).1).hom) ≫ q =
      (conjugatingDataOverQuotient q hq h).2.1.hom ≫ (i' ≫ q) :=
  (conjugatingDataOverQuotient q hq h).2.2

end ArbitraryBase

section Field

variable {k : Type u} [Field k]
variable {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- A quotient with rational-point lifting reduces maximal-torus conjugacy to
the equal-quotient-map case with the same source torus. Preservation of full
maximality and that residual case remain explicit hypotheses. -/
theorem maximalToriAreConjugate_of_quotient
    (q : G ⟶ Q)
    (hq : Function.Surjective
      (fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X => g ≫ q.hom.hom))
    (hmax : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalTorus i → IsMaximalTorus (i ≫ q))
    (hQ : MaximalToriAreConjugate Q)
    (hfiber : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i j : T.toGrp ⟶ G), IsMaximalTorus i → IsMaximalTorus j →
        i ≫ q = j ≫ q → SubgroupConjugate i j) :
    MaximalToriAreConjugate G := by
  intro T T' i i' hi hi'
  let d := conjugatingDataOverQuotient q hq
    (hQ T T' (i ≫ q) (i' ≫ q) (hmax T i hi) (hmax T' i' hi'))
  have halign :
      (i ≫ (G.innerIso d.1).hom) ≫ q = (d.2.1.hom ≫ i') ≫ q := by
    simpa only [Category.assoc] using d.2.2
  have hf := hfiber T (i ≫ (G.innerIso d.1).hom) (d.2.1.hom ≫ i')
    (hi.comp_iso (G.innerIso d.1)) (hi'.iso_comp d.2.1) halign
  exact ((SubgroupConjugate.conjugate i d.1).trans hf).trans
    (SubgroupConjugate.iso_source d.2.1 i')

/-- A scheme section supplies the rational-point lifting in the quotient
reduction, without imposing a group law on the section. -/
theorem maximalToriAreConjugate_of_quotient_section
    (q : G ⟶ Q) (s : Q.X ⟶ G.X) (hs : s ≫ q.hom.hom = 𝟙 Q.X)
    (hmax : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalTorus i → IsMaximalTorus (i ≫ q))
    (hQ : MaximalToriAreConjugate Q)
    (hfiber : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i j : T.toGrp ⟶ G), IsMaximalTorus i → IsMaximalTorus j →
        i ≫ q = j ≫ q → SubgroupConjugate i j) :
    MaximalToriAreConjugate G :=
  maximalToriAreConjugate_of_quotient q
    (points_surjective_of_scheme_section q s hs _) hmax hQ hfiber

end Field

end Langlands.GroupScheme
