import Langlands.GroupScheme.IdentityJetBaseChange
import Langlands.GroupScheme.IdentityJetFiniteProjection
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.CocharacterTransport

/-! # Functoriality and base change of actual separated group identity jets -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityJet

variable {S T : Scheme.{u}}

private theorem ideal_comap_le {G H : GroupScheme S} (f : G ⟶ H) (n : ℕ) :
    (ideal H n).comap f.hom.hom.left ≤ ideal G n := by
  have h : H.identitySection.ker.comap f.hom.hom.left ≤ G.identitySection.ker := by
    apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
    rw [Scheme.IdealSheafData.map_ker, identitySection_naturality]
  change (H.identitySection.ker ^ (n + 1)).comap f.hom.hom.left ≤
    G.identitySection.ker ^ (n + 1)
  rw [idealSheaf_comap_pow]
  exact fun U => Ideal.pow_right_mono (h U) _

/-- A group homomorphism induces a map of the actual identity neighborhoods. -/
def map {G H : GroupScheme S} (f : G ⟶ H) (n : ℕ) :
    scheme G n ⟶ scheme H n :=
  Scheme.IdealSheafData.subschemeMap (ideal G n) (ideal H n) f.hom.hom.left
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr (ideal_comap_le f n))

@[reassoc (attr := simp)]
theorem map_inclusion {G H : GroupScheme S} (f : G ⟶ H) (n : ℕ) :
    map f n ≫ inclusion H n = inclusion G n ≫ f.hom.hom.left :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

@[reassoc (attr := simp)]
theorem map_projection {G H : GroupScheme S} (f : G ⟶ H) (n : ℕ) :
    map f n ≫ projection H n = projection G n := by
  simp [projection]

/-- The order-`n` actual identity neighborhood as a functor over the base. -/
def schemeFunctor (S : Scheme.{u}) (n : ℕ) : GroupScheme S ⥤ Over S where
  obj G := Over.mk (projection G n)
  map f := Over.homMk (map f n) (map_projection f n)
  map_id G := by
    apply Over.OverMorphism.ext
    change map (𝟙 G) n = 𝟙 (scheme G n)
    rw [← cancel_mono (inclusion G n)]
    simp
  map_comp f g := by
    apply Over.OverMorphism.ext
    change map (f ≫ g) n = map f n ≫ map g n
    rw [← cancel_mono (inclusion _ n)]
    simp

/-- Conjugation by a base point gives an automorphism of the actual identity neighborhood. -/
def conjugationAut (G : GroupScheme S) (n : ℕ) :
    (Over.mk (𝟙 S) ⟶ G.X) →* Aut ((schemeFunctor S n).obj G) :=
  ((schemeFunctor S n).mapAut G).comp G.innerAut

@[reassoc (attr := simp)]
theorem conjugationAut_inclusion (G : GroupScheme S) (n : ℕ)
    (g : Over.mk (𝟙 S) ⟶ G.X) :
    (conjugationAut G n g).asIso.hom.left ≫ inclusion G n =
      inclusion G n ≫ (G.innerIso g).hom.hom.hom.left :=
  map_inclusion (G.innerIso g).hom n

variable (G : GroupScheme S) (b : T ⟶ S) [IsSeparated G.X.hom]

/-- Pulling back the actual identity jet ideal gives the actual ideal of the base-changed group. -/
theorem ideal_baseChange_of_separated (n : ℕ) :
    (ideal G n).comap (pullback.fst G.X.hom b) =
      ideal ((GroupScheme.baseChange b).obj G) n := by
  let : IsClosedImmersion G.identitySection := by
    have : IsClosedImmersion (G.identitySection ≫ G.X.hom) := by
      rw [G.identitySection_comp]
      infer_instance
    exact IsClosedImmersion.of_comp G.identitySection G.X.hom
  have h := identitySection_isPullback G b
  have hker :
      G.identitySection.ker.comap (pullback.fst G.X.hom b) =
        ((GroupScheme.baseChange b).obj G).identitySection.ker := by
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      ← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
  change (G.identitySection.ker ^ (n + 1)).comap (pullback.fst G.X.hom b) = _
  rw [idealSheaf_comap_pow, hker]
  rfl

/-- The scheme map from the actual identity neighborhood after arbitrary change of base. -/
def separatedBaseChangeMap (n : ℕ) :
    scheme ((GroupScheme.baseChange b).obj G) n ⟶ scheme G n :=
  Scheme.IdealSheafData.subschemeMap
    (ideal ((GroupScheme.baseChange b).obj G) n) (ideal G n)
    (pullback.fst G.X.hom b)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr
      (le_of_eq (ideal_baseChange_of_separated G b n)))

@[reassoc (attr := simp)]
theorem separatedBaseChangeMap_inclusion (n : ℕ) :
    separatedBaseChangeMap G b n ≫ inclusion G n =
      inclusion ((GroupScheme.baseChange b).obj G) n ≫ pullback.fst G.X.hom b :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- Identity neighborhoods of separated groups form the cartesian base-change square. -/
theorem separatedBaseChange_isPullback (n : ℕ) :
    IsPullback (separatedBaseChangeMap G b n) (projection ((GroupScheme.baseChange b).obj G) n)
      (projection G n) b := by
  have h : IsPullback (inclusion ((GroupScheme.baseChange b).obj G) n)
      (separatedBaseChangeMap G b n) (pullback.fst G.X.hom b) (inclusion G n) :=
    isPullback_of_isClosedImmersion _ _ _ _
      (separatedBaseChangeMap_inclusion G b n).symm
      (by simpa only [inclusion, Scheme.IdealSheafData.ker_subschemeι] using
        ideal_baseChange_of_separated G b n)
  exact h.flip.paste_vert (IsPullback.of_hasPullback G.X.hom b)

/-- The jet of the changed group identifies over the new base with the pulled-back jet. -/
def separatedBaseChangeOverIso (n : ℕ) :
    (schemeFunctor T n).obj ((GroupScheme.baseChange b).obj G) ≅
      (Over.pullback b).obj ((schemeFunctor S n).obj G) :=
  Over.isoMk (separatedBaseChange_isPullback G b n).isoPullback
    (separatedBaseChange_isPullback G b n).isoPullback_hom_snd

/-- Test-valued group points act by conjugation on the pullback of the actual jet. -/
def baseChangedConjugationAut (n : ℕ) :
    (Over.mk b ⟶ G.X) →* Aut ((Over.pullback b).obj ((schemeFunctor S n).obj G)) :=
  (Aut.autMulEquivOfIso (separatedBaseChangeOverIso G b n)).toMonoidHom.comp
    ((conjugationAut ((GroupScheme.baseChange b).obj G) n).comp
      (baseChangeBasePointsEquiv b G).symm.toMonoidHom)

@[reassoc (attr := simp)]
theorem baseChangedConjugationAut_inclusion (n : ℕ) (g : Over.mk b ⟶ G.X) :
    (baseChangedConjugationAut G b n g).asIso.hom.left ≫
        (separatedBaseChangeOverIso G b n).inv.left ≫
          inclusion ((GroupScheme.baseChange b).obj G) n =
    (separatedBaseChangeOverIso G b n).inv.left ≫
      inclusion ((GroupScheme.baseChange b).obj G) n ≫
        (((GroupScheme.baseChange b).obj G).innerIso
          ((baseChangeBasePointsEquiv b G).symm g)).hom.hom.hom.left := by
  let e := separatedBaseChangeOverIso G b n
  let c := conjugationAut ((GroupScheme.baseChange b).obj G) n
    ((baseChangeBasePointsEquiv b G).symm g)
  have he : (baseChangedConjugationAut G b n g).asIso.hom ≫ e.inv = e.inv ≫ c.asIso.hom := by
    change (e.inv ≫ c.asIso.hom ≫ e.hom) ≫ e.inv = _
    simp
  rw [← Category.assoc, ← Over.comp_left, he, Over.comp_left, Category.assoc]
  exact congrArg (e.inv.left ≫ ·) (conjugationAut_inclusion _ n _)

/-- The actual pushed structure module of a finite identity jet commutes with base change. -/
def separatedBaseChangeIso [LocallyOfFiniteType G.X.hom] (n : ℕ) :
    (Scheme.Modules.pullback b).obj (module G n) ≅
      module ((GroupScheme.baseChange b).obj G) n := by
  let : IsFinite (projection G n) := finite_projection G n
  have : (Langlands.SchemeModule.structureModule (scheme G n)).IsQuasicoherent :=
    Langlands.AlgebraicGeometry.Modules.CechDegreeOne.isQuasicoherent_unit _
  exact
    Langlands.AlgebraicGeometry.Modules.DerivedSections.affinePushforwardBaseChangeIso
      b (projection G n) (projection ((GroupScheme.baseChange b).obj G) n)
      (separatedBaseChangeMap G b n) (separatedBaseChange_isPullback G b n)
      (Langlands.SchemeModule.structureModule (scheme G n)) ≪≫
        (Scheme.Modules.pushforward (projection ((GroupScheme.baseChange b).obj G) n)).mapIso
          (Langlands.Scheme.Modules.pullbackUnitIso (separatedBaseChangeMap G b n))

end Langlands.GroupScheme.IdentityJet
