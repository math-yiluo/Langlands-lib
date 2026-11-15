import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps

/-! # Two steps of Murre's proof of Proposition 2

Murre (Bourbaki exp. 294) proves Proposition 2 (`MurreLocalToGlobalStatement`) by noetherian
induction on the base. In the inductive step he constructs, for every point of `F`, a
monomorphic and étale morphism `ξ : U → F` from a scheme `U` of finite type over the base
through which the point factors, and then concludes by his Lemma 3 (SGA 3, XI 3.5).
This module states the two parts separately, and their conjunction:

* `MurreChartGluingStatement`: Murre's Lemma 3, in the form of SGA 3, XI, Proposition 3.5.
* `MurreNoetherianChartsStatement`: the construction of such charts over the spectrum of a
  noetherian ring, under the noetherian induction hypothesis that `F` is representable over
  every closed subscheme strictly contained in the base.

The étaleness of a morphism `U → F` into a functor is the infinitesimal notion of SGA 3,
XI 1.6–1.8 (`InfinitesimallyEtaleAt`). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

variable {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type v)

/-- The element `ξ ∈ F(U)`, viewed as a morphism `U → F`, is a monomorphism: two
`S`-morphisms `T ⟶ U` with the same composite `T → U → F` are equal. -/
def IsMonoElement {U : Over S} (ξ : F.obj (op U)) : Prop :=
  ∀ ⦃T : Over S⦄ (h₁ h₂ : T ⟶ U), F.map h₁.op ξ = F.map h₂.op ξ → h₁ = h₂

/-- SGA 3, XI 1.7–1.8: the element `ξ ∈ F(U)`, viewed as a morphism `U → F`, is
infinitesimally étale at the point `y` of `U`. For every local artinian ring `A` over `S`,
every nilpotent ideal `J` of `A`, every `S`-morphism `u₀ : Spec (A/J) ⟶ U` sending the point
of `Spec (A/J)` to `y`, and every `v ∈ F(Spec A)` with `ξ ∘ u₀ = v|_{Spec (A/J)}`, there is
exactly one `S`-morphism `u : Spec A ⟶ U` extending `u₀` with `ξ ∘ u = v`. -/
def InfinitesimallyEtaleAt {U : Over S} (ξ : F.obj (op U)) (y : U.left) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (f : Spec (CommRingCat.of A) ⟶ S) (J : Ideal A), IsNilpotent J →
    ∀ u₀ : algebraOver f (A ⧸ J) ⟶ U, (∀ x, u₀.left x = y) →
    ∀ v : F.obj (op (Over.mk f)), F.map u₀.op ξ = F.map (algebraOverBase f (A ⧸ J)).op v →
      ∃! u : Over.mk f ⟶ U, algebraOverBase f (A ⧸ J) ≫ u = u₀ ∧ F.map u.op ξ = v

/-- Murre's Lemma 3, in the form of SGA 3, XI, Proposition 3.5. Let `S` be locally
noetherian and let `F` be a presheaf on `Over S` with `u`-small values satisfying (F1a),
(F1b), (F2) and (F3). Let `ξᵢ ∈ F(Uᵢ)` be a family indexed by a `u`-small type, with each
`Uᵢ` locally of finite type over `S` and each `ξᵢ : Uᵢ → F` a monomorphism that is
infinitesimally étale at every point. Suppose every point of `F` with values in a field
factors through some `ξᵢ`. Then `F` is represented by a scheme `Y` locally of finite type
over `S`, the morphisms `Uᵢ ⟶ Y` corresponding to the `ξᵢ` are open immersions, and their
images cover `Y`. -/
def MurreChartGluingStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (F : (Over S)ᵒᵖ ⥤ Type v),
    SmallValues F → ZariskiSheaf F → FaithfullyFlatSheaf F → FilteredColimits F →
    AdicLimits F →
    ∀ (ι : Type u) (U : ι → Over S) (ξ : ∀ i, F.obj (op (U i))),
      (∀ i, LocallyOfFiniteType (U i).hom) → (∀ i, IsMonoElement F (ξ i)) →
      (∀ i y, InfinitesimallyEtaleAt F (ξ i) y) →
      (∀ (K : Type u) [Field K] (f : Spec (CommRingCat.of K) ⟶ S)
        (η : F.obj (op (Over.mk f))), ∃ i, ∃ h : Over.mk f ⟶ U i, F.map h.op (ξ i) = η) →
      ∃ (Y : Scheme.{u}) (q : Y ⟶ S) (e : F.RepresentableBy (Over.mk q)),
        LocallyOfFiniteType q ∧ (∀ i, IsOpenImmersion (e.homEquiv.symm (ξ i)).left) ∧
          ∀ y : Y, ∃ i, y ∈ Set.range (e.homEquiv.symm (ξ i)).left

/-- The inductive step of Murre's proof of Proposition 2 over an affine noetherian base, up
to the final application of Lemma 3. Let `R` be a noetherian ring and `F` a presheaf on
`Over (Spec R)` satisfying the conditions, whose base change to `Spec 𝒪_{Spec R, s}` is
representable (by a separated, locally of finite type, formally unramified scheme) for every
point `s`, and whose base change to every closed subscheme `Spec (R/I)` with `I ≠ 0` is
representable in the same way. Then there is a family `ξᵢ ∈ F(Uᵢ)`, indexed by a `u`-small
type, with each `Uᵢ` locally of finite type and formally unramified over `Spec R` and each
`ξᵢ : Uᵢ → F` a monomorphism that is infinitesimally étale at every point, such that every
point of `F` with values in a field factors through some `ξᵢ`. -/
def MurreNoetherianChartsStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] (F : (Over (Spec R))ᵒᵖ ⥤ Type v),
    MurreConditions F →
    (∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F)) →
    (∀ I : Ideal R, I ≠ ⊥ →
      UnramifiedRepresentable (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F)) →
    ∃ (ι : Type u) (U : ι → Over (Spec R)) (ξ : ∀ i, F.obj (op (U i))),
      (∀ i, LocallyOfFiniteType (U i).hom ∧ FormallyUnramified (U i).hom ∧
        IsMonoElement F (ξ i) ∧ ∀ y, InfinitesimallyEtaleAt F (ξ i) y) ∧
      ∀ (K : Type u) [Field K] (f : Spec (CommRingCat.of K) ⟶ Spec R)
        (η : F.obj (op (Over.mk f))), ∃ i, ∃ h : Over.mk f ⟶ U i, F.map h.op (ξ i) = η

/-- The two steps together. -/
def MurreLocalToGlobalStepsStatement : Prop :=
  MurreChartGluingStatement.{u, v} ∧ MurreNoetherianChartsStatement.{u, v}

end Langlands.AlgebraicGeometry.UnramifiedFunctor
