import Langlands.GroupScheme.IdentityJetSheaf
import Langlands.AbelianScheme.LieBaseChange
import Langlands.AlgebraicGeometry.Modules.OpenCartesianDirectImageBaseChange
import Langlands.AlgebraicGeometry.Modules.PullbackUnit
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Actual identity jets under open change of base -/

noncomputable section

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.IdentityJet

private theorem ideal_comap_pow_equiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal B) (n : ℕ) :
    (I ^ n).comap (e : A →+* B) = (I.comap (e : A →+* B)) ^ n := by
  calc
    _ = (I ^ n).map e.symm := (Ideal.map_symm e).symm
    _ = (I.map e.symm) ^ n := by rw [Ideal.map_pow]
    _ = _ := congrArg (fun J => J ^ n) (Ideal.map_symm e)

/-- Pullback of an ideal sheaf along an open immersion commutes with its powers. -/
theorem idealSheaf_comap_pow_open {X Y : Scheme.{u}} (I : Y.IdealSheafData)
    (i : X ⟶ Y) [IsOpenImmersion i] (n : ℕ) :
    (I ^ n).comap i = (I.comap i) ^ n := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  exact ideal_comap_pow_equiv (i.appIso U).symm.commRingCatIsoToRingEquiv _ n

variable {S T : Scheme.{u}} (G : GroupScheme S) (b : T ⟶ S)

/-- The identity square of an actual base-changed group is cartesian. -/
theorem identitySection_isPullback :
    IsPullback ((GroupScheme.baseChange b).obj G).identitySection b
      (pullback.fst G.X.hom b) G.identitySection := by
  have ho : IsPullback
      (((GroupScheme.baseChange b).obj G).identitySection ≫
        ((GroupScheme.baseChange b).obj G).X.hom)
      b b (G.identitySection ≫ G.X.hom) := by
    rw [GroupScheme.identitySection_comp, GroupScheme.identitySection_comp]
    exact IsPullback.of_id_fst
  exact ho.of_right (identitySection_baseChange_fst b G)
    (IsPullback.of_hasPullback G.X.hom b).flip

variable [IsAffineHom G.X.hom] [IsOpenImmersion b]

private theorem identity_ker_comap :
    G.identitySection.ker.comap (pullback.fst G.X.hom b) =
      ((GroupScheme.baseChange b).obj G).identitySection.ker := by
  have : IsOpenImmersion (pullback.fst G.X.hom b) :=
    MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ inferInstance
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  exact (Scheme.ker_ideal_of_isPullback_of_isOpenImmersion G.identitySection
    ((GroupScheme.baseChange b).obj G).identitySection b (pullback.fst G.X.hom b)
    (identitySection_isPullback G b) U).symm

/-- The actual identity jet ideal restricts to the actual identity jet ideal. -/
theorem ideal_openBaseChange (n : ℕ) :
    (ideal G n).comap (pullback.fst G.X.hom b) =
      ideal ((GroupScheme.baseChange b).obj G) n := by
  have : IsOpenImmersion (pullback.fst G.X.hom b) :=
    MorphismProperty.pullback_fst (P := @IsOpenImmersion) _ _ inferInstance
  change (G.identitySection.ker ^ (n + 1)).comap (pullback.fst G.X.hom b) = _
  rw [idealSheaf_comap_pow_open, identity_ker_comap]
  rfl

/-- The map from the actual identity neighborhood after an open base change. -/
def openBaseChangeMap (n : ℕ) :
    scheme ((GroupScheme.baseChange b).obj G) n ⟶ scheme G n :=
  Scheme.IdealSheafData.subschemeMap
    (ideal ((GroupScheme.baseChange b).obj G) n) (ideal G n)
    (pullback.fst G.X.hom b)
    (Scheme.IdealSheafData.le_map_iff_comap_le.mpr (le_of_eq (ideal_openBaseChange G b n)))

@[reassoc (attr := simp)]
theorem openBaseChangeMap_inclusion (n : ℕ) :
    openBaseChangeMap G b n ≫ inclusion G n =
      inclusion ((GroupScheme.baseChange b).obj G) n ≫ pullback.fst G.X.hom b :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- Actual identity neighborhoods form the cartesian square for an open base change. -/
theorem openBaseChange_isPullback (n : ℕ) :
    IsPullback (openBaseChangeMap G b n) (projection ((GroupScheme.baseChange b).obj G) n)
      (projection G n) b := by
  have : IsClosedImmersion (inclusion G n) :=
    inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  have : IsClosedImmersion (inclusion ((GroupScheme.baseChange b).obj G) n) :=
    inferInstanceAs (IsClosedImmersion (ideal ((GroupScheme.baseChange b).obj G) n).subschemeι)
  have h : IsPullback (inclusion ((GroupScheme.baseChange b).obj G) n)
      (openBaseChangeMap G b n) (pullback.fst G.X.hom b) (inclusion G n) :=
    isPullback_of_isClosedImmersion _ _ _ _
      (openBaseChangeMap_inclusion G b n).symm
      (by simpa only [inclusion, Scheme.IdealSheafData.ker_subschemeι] using
        ideal_openBaseChange G b n)
  exact h.flip.paste_vert (IsPullback.of_hasPullback G.X.hom b)

/-- The actual jet module pulls back to the actual jet module along an open immersion. -/
def openBaseChangeIso (n : ℕ) :
    (Scheme.Modules.pullback b).obj (module G n) ≅
      module ((GroupScheme.baseChange b).obj G) n := by
  have : IsOpenImmersion (openBaseChangeMap G b n) :=
    MorphismProperty.of_isPullback (openBaseChange_isPullback G b n).flip inferInstance
  exact
    Langlands.AlgebraicGeometry.Modules.DerivedSections.openCartesianBaseChangeIso
      b (projection G n) (projection ((GroupScheme.baseChange b).obj G) n)
      (openBaseChangeMap G b n) (openBaseChange_isPullback G b n)
      (Langlands.SchemeModule.structureModule (scheme G n)) ≪≫
        (Scheme.Modules.pushforward (projection ((GroupScheme.baseChange b).obj G) n)).mapIso
          (Langlands.Scheme.Modules.pullbackUnitIso (openBaseChangeMap G b n))

end Langlands.GroupScheme.IdentityJet
