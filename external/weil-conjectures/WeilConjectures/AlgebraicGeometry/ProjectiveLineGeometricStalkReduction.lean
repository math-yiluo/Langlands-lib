/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison

/-!
# Reduction of the geometric-stalk exchange to the strict-local exchange

Source: Stacks Project, proof of Theorem 59.91.11 (Tag 095T), paragraphs 3--4;
blueprint geometric-stalk lemma, its strict-henselization upper square.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

/-- It suffices to identify the exchange for local maps of strictly henselian local rings.
The premise is precisely the existing strict-local exchange statement, for every pair
of strictly henselian bases and every degree. The conclusion applies it to the strict
henselizations of the two arbitrary bases. This reduction must use the canonical
restriction maps; it must not use projective-line base change or curve invariance.

Source: Stacks Project, proof of Theorem 59.91.11 (Tag 095T), paragraphs 3--4,
and the blueprint geometric-stalk lemma, proof of the upper commutative square.
(blueprint: lem-weil-pbc-p1-geometric-stalk-strict-local-reduction).

Proof: choose a common algebraic closure extending the field map contravariantly
associated to iota. Form the strict henselizations A and B at the induced geometric
points of S and T. Functoriality gives a local map A to B whose residue-field map
agrees with iota after the residue-field embeddings. The strict-henselization stalk
formula computes the higher-direct-image stalks as cohomology of the two strict-local
projective lines. Equivalently, restricting the higher-direct-image sheaves to these
strict-local bases preserves the relevant stalks: both are the same filtered colimit
of neighbourhood cohomology. For the inverse-image source first use the natural
inverse-image stalk identification. Identify the arbitrary pullback X' with the
projective line over T by the universal property of the pullback.

The exchange maps agree under these stalk comparisons. Indeed, represent F by an
injective resolution and its inverse image by a comparison resolution. On each
pointed etale neighbourhood the exchange pulls a section back along the base-changed
neighbourhood. The strict-henselization limit projections commute with the local map
A to B. Thus restricting this section to the target strict-local projective line
is identical whether one first applies the exchange or first restricts to A and
then applies the strict-local exchange. The equality survives the colimit and homology.
Apply hLocal to A, B, their local map and the restriction of F; inverse image preserves
torsion. Its two closed-fibre comparisons identify this strict-local
exchange with residue-field pullback. The integral hypotheses imply that the chosen
separably closed fields are purely inseparable algebraic extensions of the corresponding
separable closures of the image residue fields. Topological invariance therefore
identifies the residue closed fibres with the projective lines over k and k'.
Compose these cohomology identifications with the stalk comparisons. Functoriality
of pullback and compatibility of the residue-field square give exactly the displayed
identity along iota, and composites of additive equivalences give e1 and e2.
The construction also works in degree zero, for zero sheaves and for purely inseparable
nontrivial residue-field extensions; it needs no smoothness or perfectness hypothesis. -/
theorem Etale.geometricStalk_projectiveLine_of_strictLocal
    (Λ : Type (u + 1)) [CommRing Λ]
    (hLocal : ∀ (A B : Type u) [CommRing A] [HenselianLocalRing A]
      [IsSepClosed (IsLocalRing.ResidueField A)] [CommRing B] [HenselianLocalRing B]
      [IsSepClosed (IsLocalRing.ResidueField B)] (φ : A →+* B) [IsLocalHom φ]
      (F : Sheaf (ProjectiveLine (Spec (.of A))).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)) [IsTorsionModuleSheaf F] (q : ℕ),
      ∃ (e₁ : ((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ (Spec.map (CommRingCat.ofHom φ))
            (ProjectiveLine (Spec (.of A)) ↘ Spec (.of A)) q).obj F) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
            (IsLocalRing.residue A))))^*[ModuleCat.{u + 1} Λ].obj F)) q)
      (e₂ : ((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom φ)))
            (ProjectiveLine (Spec (.of B)) ↘ Spec (.of B)) q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
            (IsLocalRing.ResidueField.map φ))))^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
              (IsLocalRing.residue A))))^*[ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, e₂ ((((pointSmallEtale (Spec.map (CommRingCat.ofHom (IsLocalRing.residue B)))).sheafFiber
          (A := ModuleCat.{u + 1} Λ)).map (Etale.baseChangeHomologyMap Λ
            (ProjectiveSpace.isPullback_map _ (Spec.map (CommRingCat.ofHom φ))) q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
            (IsLocalRing.ResidueField.map φ))))
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ (Spec.map (CommRingCat.ofHom
              (IsLocalRing.residue A))))^*[ModuleCat.{u + 1} Λ].obj F)) q (e₁ x))
    {S T X' : Scheme.{u}} {g : T ⟶ S} {f' : X' ⟶ T} {g' : X' ⟶ ProjectiveLine S}
    (sq : IsPullback g' f' (ProjectiveLine S ↘ S) g)
    {k k' : Type u} [Field k] [IsSepClosed k] [Field k'] [IsSepClosed k']
    (σ : Spec (.of k) ⟶ S) (τ : Spec (.of k') ⟶ T) (ι : Spec (.of k') ⟶ Spec (.of k))
    (hι : ι ≫ σ = τ ≫ g)
    (hσ : ∃ (s : S) (φ : S.residueField s ⟶ .of k),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ S.fromSpecResidueField s = σ)
    (hτ : ∃ (t : T) (φ : T.residueField t ⟶ .of k'),
      φ.hom.IsIntegral ∧ Spec.map φ ≫ T.fromSpecResidueField t = τ)
    (F : Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsTorsionModuleSheaf F] (q : ℕ) :
    ∃ (e₁ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeSourceFunctor Λ g (ProjectiveLine S ↘ S) q).obj F) ≃+
        Sheaf.H ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
          ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q)
      (e₂ : ((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
          ((Etale.baseChangeTargetFunctor Λ g' f' q).obj F) ≃+
        Sheaf.H ((ProjectiveSpace.map _ ι)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F))) q),
      ∀ x, e₂ ((((pointSmallEtale τ).sheafFiber (A := ModuleCat.{u + 1} Λ)).map
          (Etale.baseChangeHomologyMap Λ sq q F)).hom x) =
        Etale.cohomologyMap (ProjectiveSpace.map _ ι)
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
            ((ProjectiveSpace.map _ σ)^*[ModuleCat.{u + 1} Λ].obj F)) q (e₁ x) := by
  obtain ⟨A, B, cA, cB, hmodel⟩ :=
    Etale.projectiveLine_strictLocal_modelComparison Λ sq σ τ ι hι hσ hτ F q
  letI := cA
  letI := cB
  obtain ⟨hA, hB, hmodel⟩ := hmodel
  letI := hA
  letI := hB
  obtain ⟨sA, sB, hmodel⟩ := hmodel
  letI := sA
  letI := sB
  obtain ⟨φ, hφ, hmodel⟩ := hmodel
  letI := hφ
  obtain ⟨F₀, hF₀, a₁, a₂, b₁, b₂, ha, hb⟩ := hmodel
  letI := hF₀
  obtain ⟨e₁, e₂, he⟩ := hLocal A B φ F₀ q
  refine ⟨(a₁.trans e₁).trans b₁, (a₂.trans e₂).trans b₂, ?_⟩
  intro x
  change b₂ (e₂ (a₂ _)) = _
  rw [ha, he, hb]
  rfl

end AlgebraicGeometry
