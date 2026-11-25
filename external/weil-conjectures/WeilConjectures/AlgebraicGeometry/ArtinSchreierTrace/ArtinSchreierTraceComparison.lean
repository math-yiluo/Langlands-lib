/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.Finite.Trace

/-! # The trace comparison between the two Artin–Schreier models

Source: latest blueprint, sec-fourier-transform/sk-lem-as-properties,
lemma-artin-schreier-character-sheaf, clauses (1)–(3) and its proof
(blueprint: lemma-artin-schreier-character-sheaf).

The cover is the existing polynomial-quotient cover, also for exponent q.
The maps on direct images are the actual pullbacks of coefficient sections.
The condensed version uses internal modules over the pulled-back coefficient ring;
its scalars are global sections of the condensed ring, that is, its value at the point.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ArtinSchreierTrace

attribute [local irreducible] ProEtale.CondensedRing.upperStar
  ProEtale.CondensedRing.upperStarLowerStarAdjunction

/-- The image of a scalar in the structure sheaf of a k-scheme.
Source: blueprint lemma-artin-schreier-character-sheaf (2), the function af
(blueprint: lemma-artin-schreier-character-sheaf). -/
def scalar (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (a : k) : Γ(X, ⊤) :=
  (X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv.hom a)

/-- The constant coefficient module, retaining its actual internal-module structure.
Source: blueprint lemma-artin-schreier-character-sheaf, condensed coefficient paragraph
(blueprint: lemma-artin-schreier-character-sheaf). -/
def condensedUnit (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :=
  Mod.regular (ProEtale.condensedRingObj Λ X)

/-- Pullback of condensed coefficient sections as a morphism of coefficient modules.
The linear lift sends 1 to the canonical coefficient unit eta_h(1); hence it is eta_h.
Source: blueprint lemma-artin-schreier-character-sheaf (2), coefficient-module h_a^*
(blueprint: lemma-artin-schreier-character-sheaf). -/
@[irreducible]
def condensedPull (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}} {Y Z : Over X} (h : Y ⟶ Z) :
    (ProEtale.CondensedRing.lowerStar Λ Z.hom).obj (condensedUnit Λ Z.left) ⟶
      (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left) :=
  (ProEtale.CondensedRing.lowerStar Λ Z.hom).map
      (Mod.regularLift
        ((ProEtale.CondensedRing.lowerStar Λ h.left).obj (condensedUnit Λ Y.left))
        (MonObj.one ≫ ProEtale.condensedPushforwardHom Λ h.left)) ≫
    (ProEtale.CondensedRing.lowerStarComp Λ h.left Z.hom).hom.app _ ≫
      (ProEtale.CondensedRing.lowerStarCongr Λ (Over.w h)).hom.app _

/-- The condensed averaging projector. Each coefficient is first transported by p_Y^*
and then acts on the regular coefficient module, before direct image.
Source: blueprint lemma-artin-schreier-character-sheaf, explicit projector e_chi
(blueprint: lemma-artin-schreier-character-sheaf). -/
@[irreducible]
def condensedProjector (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (G : Type v) [AddGroup G] [Fintype G]
    {X : Scheme.{u}} (Y : Over X) (σ : G → (Y ⟶ Y)) (χ : AddChar G (MonObj.Γ Λ)) :
    End ((ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)) :=
  ∑ c : G, End.of (condensedPull Λ (σ c) ≫
    (ProEtale.CondensedRing.lowerStar Λ Y.hom).map
      (Mod.regularEndRingHom (MonObj.Γ.mapFunctorMonoidHom (ProEtale.upperStarFromPoint Y.left)
        (Ring.inverse (Fintype.card G : MonObj.Γ Λ) * χ (-c)))).asHom)

/-- Evaluation of a condensed eigensection at a chosen root, in internal modules.
Source: blueprint lemma-artin-schreier-character-sheaf (3), evaluation trivializations
(blueprint: lemma-artin-schreier-character-sheaf). -/
@[irreducible]
def condensedEvaluation (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X T : Scheme.{u}} (x : T ⟶ X)
    {Y : Over X} (s : Over.mk x ⟶ Y)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (ProEtale.condensedRingObj Λ X)}
    (ι : M ⟶ (ProEtale.CondensedRing.lowerStar Λ Y.hom).obj (condensedUnit Λ Y.left)) :
    (ProEtale.CondensedRing.upperStar Λ x).obj M ⟶ condensedUnit Λ T :=
  (ProEtale.CondensedRing.upperStar Λ x).map (ι ≫ condensedPull Λ s) ≫
    (ProEtale.CondensedRing.upperStarLowerStarAdjunction Λ x).counit.app (condensedUnit Λ T)

/-- The degree-q Artin–Schreier sheaf with condensed coefficients. The same universal
Artin–Schreier map and translations as in the recorded etale definition are used;
only the coefficient category is changed to the recorded internal modules.
Source: blueprint lemma-artin-schreier-character-sheaf, condensed coefficient convention and (2)
(blueprint: lemma-artin-schreier-character-sheaf). -/
@[irreducible]
def condensedSheafOf (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]
    (χ : AddChar k (MonObj.Γ Λ)) (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (f : Γ(X, ⊤)) :=
  (ProEtale.CondensedRing.upperStar Λ
    (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ : PUnit ↦ f)).obj
      (image (condensedProjector Λ k
        (Over.mk (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k)))
        (fun c ↦ Over.homMk (Etale.artinSchreierTranslation k c)
          (Etale.artinSchreierTranslation_comp_artinSchreierMap k c)) χ).asHom)

end AlgebraicGeometry.ArtinSchreierTrace
