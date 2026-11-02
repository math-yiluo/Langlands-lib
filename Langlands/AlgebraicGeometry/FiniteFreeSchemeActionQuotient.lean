import Langlands.AlgebraicGeometry.FiniteFreeSchemeActionRelation
import Langlands.AlgebraicGeometry.FiniteLocallyFreeEquivalenceRelationAffineQuotientProof
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Finiteness.Basic

/-! # Affine quotients of finite free scheme actions -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

namespace Langlands.AlgebraicGeometry.FiniteFreeSchemeAction

variable {G : Type u} [Group G] {X : Scheme.{u}} (A : FiniteFreeSchemeAction G X)

section Construction

variable [Finite G] [IsAffine X]

instance source_isFinite : IsFinite A.source := by
  let B := Γ(X, ⊤)
  let d : CommRingCat.of B ⟶ CommRingCat.of (G → B) :=
    CommRingCat.ofHom (algebraMap B (G → B))
  have : IsFinite (Spec.map d) :=
    (IsFinite.SpecMap_iff d).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have h : A.source =
      (Sigma.mapIso (fun _ : G => X.isoSpec)).hom ≫
        sigmaSpec (fun _ : G => Γ(X, ⊤)) ≫ Spec.map d ≫ X.isoSpec.inv := by
    apply Sigma.hom_ext
    intro g
    simp only [Sigma.ι_mapIso_hom_assoc, ι_sigmaSpec_assoc,
      ← Spec.map_comp_assoc]
    have hd : d ≫ CommRingCat.ofHom (Pi.evalRingHom (fun _ : G => B) g) = 𝟙 _ := by
      ext b
      rfl
    rw [hd]
    rw [A.ι_source, Spec.map_id]
    change 𝟙 X = X.isoSpec.hom ≫ 𝟙 (Spec Γ(X, ⊤)) ≫ X.isoSpec.inv
    simp
  rw [h]
  infer_instance

instance target_isFinite : IsFinite A.target := by
  have h : A.target = (Sigma.mapIso A.act).hom ≫ A.source := by
    apply Sigma.hom_ext
    intro g
    simp
  rw [h]
  infer_instance

/-- An affine quotient, with its effective relation and coequalizer property. -/
structure AffineQuotient where
  scheme : Scheme.{u}
  isAffine : IsAffine scheme
  map : X ⟶ scheme
  condition : A.target ≫ map = A.source ≫ map
  finite : IsFinite map
  etale : Etale map
  surjective : Surjective map
  isPullback : IsPullback A.target A.source map map
  isColimit : IsColimit (Cofork.ofπ map condition)

attribute [instance] AffineQuotient.isAffine AffineQuotient.finite
  AffineQuotient.etale AffineQuotient.surjective

/-- Existence follows from the published finite locally free affine quotient
theorem; étaleness descends from a projection of the effective relation. -/
theorem nonempty_affineQuotient : Nonempty A.AffineQuotient := by
  have hj : ∀ {T : Scheme.{u}} (a b : T ⟶ A.relationScheme),
      a ≫ A.target = b ≫ A.target → a ≫ A.source = b ≫ A.source → a = b := by
    intro T a b ht hs
    apply (cancel_mono (prod.lift A.target A.source)).mp
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.lift_fst] using ht
    · simpa only [Category.assoc, prod.lift_snd] using hs
  have he : ∀ T : Scheme.{u}, _root_.Equivalence
      (fun x y : T ⟶ X => ∃ r : T ⟶ A.relationScheme,
        r ≫ A.target = x ∧ r ≫ A.source = y) := by
    intro T
    refine ⟨A.reflexive T, ?_, ?_⟩
    · rintro x y ⟨r, hx, hy⟩
      obtain ⟨r', h1, h2⟩ := A.symmetric T r
      exact ⟨r', h1.trans hy, h2.trans hx⟩
    · rintro x y z ⟨r, hx, hy⟩ ⟨r', hy', hz⟩
      obtain ⟨r'', h1, h2⟩ := A.transitive T r r' (hy.trans hy'.symm)
      exact ⟨r'', h1.trans hx, h2.trans hz⟩
  obtain ⟨Y, hY, q, w, hfin, hflat, hlfp, hsurj, hpb, ⟨hc⟩⟩ :=
    FiniteLocallyFreeQuotient.existsAffineQuotient A.target A.source hj he
  have : IsFinite q := hfin
  have : Flat q := hflat
  have : Surjective q := hsurj
  have hq : Etale q := by
    apply MorphismProperty.of_isPullback_of_descendsAlong
      (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb
    · exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
    · infer_instance
  exact ⟨⟨Y, hY, q, w, hfin, hq, hsurj, hpb, hc⟩⟩

/-- A chosen affine quotient of the finite free action. -/
def quotient : A.AffineQuotient := Classical.choice A.nonempty_affineQuotient

end Construction

namespace AffineQuotient

variable {A} (Q : A.AffineQuotient)

@[reassoc (attr := simp)] theorem invariant (g : G) :
    (A.act g).hom ≫ Q.map = Q.map := by
  simpa using congrArg (fun f => Sigma.ι (fun _ : G => X) g ≫ f) Q.condition

/-- An invariant morphism equalizes the two maps of the action relation. -/
theorem equalizes {Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ g : G, (A.act g).hom ≫ f = f) :
    A.target ≫ f = A.source ≫ f := by
  apply Sigma.hom_ext
  intro g
  simpa using hf g

/-- Descent of a morphism invariant under the finite group action. -/
def desc {Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ g : G, (A.act g).hom ≫ f = f) : Q.scheme ⟶ Y :=
  Q.isColimit.desc (Cofork.ofπ f (equalizes (A := A) f hf))

@[reassoc (attr := simp)] theorem map_desc {Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ g : G, (A.act g).hom ≫ f = f) :
    Q.map ≫ Q.desc f hf = f :=
  Cofork.IsColimit.π_desc Q.isColimit

theorem hom_ext {Y : Scheme.{u}} (f g : Q.scheme ⟶ Y)
    (h : Q.map ≫ f = Q.map ≫ g) : f = g :=
  Cofork.IsColimit.hom_ext Q.isColimit h

end AffineQuotient

end Langlands.AlgebraicGeometry.FiniteFreeSchemeAction
