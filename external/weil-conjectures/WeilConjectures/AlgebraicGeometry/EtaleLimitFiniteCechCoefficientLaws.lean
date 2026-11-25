/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import WeilConjectures.AlgebraicGeometry.EtaleLimitFiniteCechCoefficientIdentity
import WeilConjectures.AlgebraicGeometry.EtaleLimitFiniteCechCoefficientComposition
import WeilConjectures.AlgebraicGeometry.EtaleLimitFiniteCechCoefficientLeg

/-! # Canonical coefficient maps on descended Čech complexes

Source: Stacks Project, Tags 01ZM, 07RP, 07RR and 09YP. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

-- Keep the existing signature, including its redundant geometric hypotheses.
set_option linter.unusedVariables false in
/-- Cochain maps with the specified coefficient components obey the diagram laws.
Source: Stacks Project, Tag 09YP, proof of lemma-colimit, the canonical Čech
comparison. The inverse-image unit laws are expressed in
WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence.
(blueprint: lem-weil-pbc-etale-limit-finite-cech-coefficient-laws).

Proof: Equality of cochain maps is checked in every degree, and equality of
maps into the section product is checked after every tuple projection. Cancel
the image of the target nerve isomorphism. For the identity law substitute
hidentity in the tuple formula. The inverse-image identity unit law reduces
the section map to identity followed by the canonical identity pullback
comparison; hgamma identifies gamma with that comparison by pullback
uniqueness. For composition substitute the two tuple formulas and move
presheaf restrictions past the unit and phi by naturality. Substitute
hcomposition and the unit form of upperStarComp coherence. Both geometric
pasting maps have the same first projection to W0 by hgamma and the same
structural morphism, so pullback uniqueness identifies them. This gives the
single tuple formula for the composite. For the leg equation perform the
same unit-composition calculation, now with the cone identity c.w and hdelta.
Substitute hG; cancel eG with its inverse and use L.w to replace G(a) followed
by the later leg by the earlier leg. Product and cochain-map extensionality
finish all three equations. Empty K causes no exception: all component
checks are vacuous. No existence or differential-compatibility assertion is
part of this theorem: m and l are already cochain maps.
-/
theorem etale_limit_finite_cech_coefficient_laws
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    (L : Cocone G)
    (U : c.pt.Etale)
    (K : Type (u + 1)) [Finite K] (V : K → c.pt.Etale) (f : ∀ k, V k ⟶ U)
    (i₀ : I) (U₀ : (D.obj (op i₀)).Etale)
    (V₀ : K → (D.obj (op i₀)).Etale) (f₀ : ∀ k, V₀ k ⟶ U₀)
    (eU : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj U₀ ≅ U)
    (eV : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).obj (V₀ k) ≅ V k)
    (he : ∀ k,
      (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))).map (f₀ k) ≫
        eU.hom = (eV k).hom ≫ f k) :
    let J := {j : I // i₀ ≤ j}
    let B := fun j : J ↦
      MorphismProperty.Over.pullback @Etale ⊤ (D.map (homOfLE j.property).op)
    let Blim := MorphismProperty.Over.pullback @Etale ⊤ (c.π.app (op i₀))
    let Uj := fun j : J ↦ (B j).obj U₀
    let Vj := fun (j : J) (k : K) ↦ (B j).obj (V₀ k)
    let fj := fun (j : J) (k : K) ↦ (B j).map (f₀ k)
    let W₀ := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f₀ (t a))).left
    let pr₀ := fun (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)) ↦
      (Pi.π (fun a ↦ Over.mk (f₀ (t a))) a).left
    let Wj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦ (B j).obj (W₀ n t)
    let Wlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦ Blim.obj (W₀ n t)
    let Nj := fun (j : J) (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (fj j (t a))).left
    let Nlim := fun (n : ℕ) (t : Fin (n + 1) → K) ↦
      (∏ᶜ fun a ↦ Over.mk (f (t a))).left
    let Pj := fun (j : J) (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ (F j.val).obj.obj (op (Nj j n t))
    let Plim := fun (n : ℕ) ↦
      fun t : Fin (n + 1) → K ↦ L.pt.obj.obj (op (Nlim n t))
    let Cj := fun j : J ↦
      (cechComplexFunctor (fun k : K ↦ Over.mk (fj j k))).obj
        ((Over.forget (Uj j)).op ⋙ (F j.val).obj)
    let CX := (cechComplexFunctor (fun k : K ↦ Over.mk (f k))).obj
      ((Over.forget U).op ⋙ L.pt.obj)
    ∀ (eNj : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        Wj j n t ≅ Nj j n t)
      (eNlim : ∀ (n : ℕ) (t : Fin (n + 1) → K), Wlim n t ≅ Nlim n t)
      (γ : ∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t) ≅ Wj k n t)
      (δ : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (MorphismProperty.Over.pullback @Etale ⊤
          (c.π.app (op j.val))).obj (Wj j n t) ≅ Wlim n t)
      (hNj : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNj j n t).hom ≫ (Pi.π (fun a ↦ Over.mk (fj j (t a))) a).left =
          (B j).map (pr₀ n t a))
      (hNlim : ∀ (n : ℕ) (t : Fin (n + 1) → K) (a : Fin (n + 1)),
        (eNlim n t).hom ≫ (Pi.π (fun a ↦ Over.mk (f (t a))) a).left =
          Blim.map (pr₀ n t a) ≫ (eV (t a)).hom)
      (hγ : ∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (γ j k a n t).hom.left ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE k.property).op) =
          pullback.fst (Wj j n t).hom (D.map (show j.val ⟶ k.val from a).op) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op))
      (hδ : ∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (δ j n t).hom.left ≫ pullback.fst (W₀ n t).hom (c.π.app (op i₀)) =
          pullback.fst (Wj j n t).hom (c.π.app (op j.val)) ≫
            pullback.fst (W₀ n t).hom (D.map (homOfLE j.property).op)),
      ∀ (m : ∀ (j k : J) (a : j ⟶ k), Cj j ⟶ Cj k)
        (l : ∀ j : J, Cj j ⟶ CX),
      (∀ (j k : J) (a : j ⟶ k) (n : ℕ) (t : Fin (n + 1) → K),
        (m j k a).f n ≫
            Pi.π (Pj k n) t ≫ (F k.val).obj.map (eNj k n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (D.map (show j.val ⟶ k.val from a).op)).unit.app (F j.val)).hom.app
                (op (Wj j n t)) ≫
            (φ (show j.val ⟶ k.val from a)).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (D.map (show j.val ⟶ k.val from a).op)).obj (Wj j n t))) ≫
            (F k.val).obj.map (γ j k a n t).inv.op) ∧
      (∀ (j : J) (n : ℕ) (t : Fin (n + 1) → K),
        (l j).f n ≫
            Pi.π (Plim n) t ≫ L.pt.obj.map (eNlim n t).hom.op =
          Pi.π (Pj j n) t ≫ (F j.val).obj.map (eNj j n t).hom.op ≫
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
              (c.π.app (op j.val))).unit.app (F j.val)).hom.app (op (Wj j n t)) ≫
            (eG j.val).inv.hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            (L.ι.app j.val).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤
                (c.π.app (op j.val))).obj (Wj j n t))) ≫
            L.pt.obj.map (δ j n t).inv.op) →
      (∀ j : J, m j j (𝟙 j) = 𝟙 (Cj j)) ∧
      (∀ (j k r : J) (a : j ⟶ k) (b : k ⟶ r),
        m j r (a ≫ b) = m j k a ≫ m k r b) ∧
      (∀ (j k : J) (a : j ⟶ k), m j k a ≫ l k = l j) := by
  dsimp
  intro eNj eNlim γ δ hNj hNlim hγ hδ m l hml
  exact ⟨etale_limit_finite_cech_coefficient_identity D c F φ hidentity hcomposition
      G eG hG L U K V f i₀ U₀ V₀ f₀ eU eV he
      eNj eNlim γ δ hNj hNlim hγ hδ m l hml,
    etale_limit_finite_cech_coefficient_composition D c F φ hidentity hcomposition
      G eG hG L U K V f i₀ U₀ V₀ f₀ eU eV he
      eNj eNlim γ δ hNj hNlim hγ hδ m l hml,
    etale_limit_finite_cech_coefficient_leg D c F φ hidentity hcomposition
      G eG hG L U K V f i₀ U₀ V₀ f₀ eU eV he
      eNj eNlim γ δ hNj hNlim hγ hδ m l hml⟩

end AlgebraicGeometry.Etale
