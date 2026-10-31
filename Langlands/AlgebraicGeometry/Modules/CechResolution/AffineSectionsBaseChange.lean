import Langlands.AlgebraicGeometry.Modules.CechResolution.SectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.AffineCartesianSectionsBaseChange
import Langlands.AlgebraicGeometry.Modules.DerivedRestriction
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Canonical scalar sections on affine Čech factors -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open scoped TensorProduct ChangeOfRings

namespace Langlands.AlgebraicGeometry.Modules.CechResolution

open AlgebraicGeometry.Scheme.Modules

private lemma restrict_unit_hom_ext {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : X.Modules) (P : U.Modules)
    {a b : (pushforward j).obj ((restrictFunctor j).obj M) ⟶ (pushforward j).obj P}
    (h : (restrictAdjunction j).unit.app M ≫ a =
      (restrictAdjunction j).unit.app M ≫ b) : a = b := by
  obtain ⟨a', rfl⟩ := (pushforward j).map_surjective a
  obtain ⟨b', rfl⟩ := (pushforward j).map_surjective b
  exact congrArg (pushforward j).map (((restrictAdjunction j).homEquiv _ _).injective h)

variable {X Y Z Z' : Scheme.{u}} (g : Y ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ Y)
  (k : Z' ⟶ Z) (sq : k ≫ i = i' ≫ g) [IsOpenImmersion i] [IsOpenImmersion i']

/-- The unit for the restricted map, with restriction and square comparisons. -/
def restrictedUnitPushforward (M : X.Modules) :
    (pushforward i).obj ((restrictFunctor i).obj M) ⟶
      (pushforward g).obj ((pushforward i').obj ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))) := by
  let a := (pushforward i).map ((restrictFunctorIsoPullback i).hom.app M)
  let b := (pushforward i).map ((pullbackPushforwardAdjunction k).unit.app
    ((Scheme.Modules.pullback i).obj M))
  let c := (pushforward i).map ((pushforward k).map
    ((pullbackSquareIso g i i' k sq).hom.app M))
  let d : (pushforward i).obj ((pushforward k).obj
      ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))) ⟶
      (pushforward g).obj ((pushforward i').obj ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))) :=
    (pushforwardSquareIso g i i' k sq).hom.app ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))
  exact a ≫ b ≫ c ≫ d

variable {g i i' k sq}

/-- Restriction units detect the comparison induced by the restricted pullback unit. -/
lemma restrictedUnitPushforward_eq (M : X.Modules)
    (a : (pushforward i).obj ((restrictFunctor i).obj M) ⟶
      (pushforward g).obj ((pushforward i').obj ((restrictFunctor i').obj ((Scheme.Modules.pullback g).obj M))))
    (ha : (restrictAdjunction i).unit.app M ≫ a =
      (pullbackPushforwardAdjunction g).unit.app M ≫
        (pushforward g).map ((restrictAdjunction i').unit.app ((Scheme.Modules.pullback g).obj M))) :
    a ≫ (pushforward g).map ((pushforward i').map
        ((restrictFunctorIsoPullback i').hom.app ((Scheme.Modules.pullback g).obj M))) =
      restrictedUnitPushforward g i i' k sq M := by
  let r := (pushforwardSquareIso g i i' k sq).app
    ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M))
  rw [← cancel_mono r.inv]
  apply restrict_unit_hom_ext i M
    ((pushforward k).obj ((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback g).obj M)))
  have hj := Langlands.Scheme.Modules.restrictAdjunction_unit_restrictFunctorIsoPullback i M
  have hj' := Langlands.Scheme.Modules.restrictAdjunction_unit_restrictFunctorIsoPullback i'
    ((Scheme.Modules.pullback g).obj M)
  have hs := unit_comp_pushforwardSquareIso_eq g i i' k sq M
  have he : (restrictAdjunction i).unit.app M ≫
      (a ≫ (pushforward g).map ((pushforward i').map
        ((restrictFunctorIsoPullback i').hom.app ((Scheme.Modules.pullback g).obj M)))) =
      (restrictAdjunction i).unit.app M ≫ restrictedUnitPushforward g i i' k sq M := by
    dsimp only [restrictedUnitPushforward]
    rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp, hj']
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hj]
    exact hs.symm
  simpa only [Category.assoc] using congrArg (fun b => b ≫ r.inv) he

variable (g) (M : X.Modules) {W : X.Opens} {W' : Y.Opens} (hW : W' ≤ g ⁻¹ᵁ W)

/-- The actual factor map agrees with the unit on the restricted square. -/
lemma sheafOnPushforward_pullbackUnit_comp
    (k : (W' : Scheme) ⟶ (W : Scheme)) (sq : k ≫ W.ι = W'.ι ≫ g) :
    sheafOnPushforward g ((pullbackPushforwardAdjunction g).unit.app M) hW ≫
        (pushforward g).map ((pushforward W'.ι).map
          ((restrictFunctorIsoPullback W'.ι).hom.app ((Scheme.Modules.pullback g).obj M))) =
      restrictedUnitPushforward g W.ι W'.ι k sq M :=
  restrictedUnitPushforward_eq M _
    (unit_sheafOnPushforward g ((pullbackPushforwardAdjunction g).unit.app M) hW)


/-- Sections of an open factor identified with sections of the actual pullback. -/
def factorPullbackSectionsIso {T : CommRingCat.{u}} (f : X ⟶ Spec T)
    (M : X.Modules) (W : X.Opens) :
    (relativeGlobalSections f).obj (sheafOn M W) ≅
      (relativeGlobalSections (W.ι ≫ f)).obj ((Scheme.Modules.pullback W.ι).obj M) :=
  (relativeGlobalSections f).mapIso
      ((pushforward W.ι).mapIso ((restrictFunctorIsoPullback W.ι).app M)) ≪≫
    (relativeGlobalSectionsCompIso W.ι f).app ((Scheme.Modules.pullback W.ι).obj M)

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (f : X ⟶ Spec R) (f' : Y ⟶ Spec S)
  (w : g ≫ f = f' ≫ Spec.map φ)

/-- The ordinary factor map is the canonical sections map for the restricted square. -/
lemma factorSectionsMap_pullbackUnit_comp
    (k : (W' : Scheme) ⟶ (W : Scheme)) (sq : k ≫ W.ι = W'.ι ≫ g) :
    factorSectionsMap φ f f' g w ((pullbackPushforwardAdjunction g).unit.app M) hW ≫
        (ModuleCat.restrictScalars φ.hom).map
          (factorPullbackSectionsIso f' ((Scheme.Modules.pullback g).obj M) W').hom =
      (factorPullbackSectionsIso f M W).hom ≫
        sectionsBaseChangeMap φ (W.ι ≫ f) (W'.ι ≫ f') k
          (square_restrict_comm φ f f' g w W.ι W'.ι k sq)
          ((Scheme.Modules.pullback W.ι).obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map
          ((relativeGlobalSections (W'.ι ≫ f')).map
            ((pullbackSquareIso g W.ι W'.ι k sq).hom.app M)) := by
  ext x
  have h := congrArg (fun a => a.app ⊤ x)
    (sheafOnPushforward_pullbackUnit_comp g M hW k sq)
  simp [restrictedUnitPushforward, pushforwardSquareIso] at h
  exact h

/-- Scalar adjunction transports the exact ordinary factor comparison. -/
lemma scalarFactorSectionsMap_pullbackUnit_comp
    (k : (W' : Scheme) ⟶ (W : Scheme)) (sq : k ≫ W.ι = W'.ι ≫ g) :
    scalarFactorSectionsMap φ f f' g w ((pullbackPushforwardAdjunction g).unit.app M) hW ≫
        (factorPullbackSectionsIso f' ((Scheme.Modules.pullback g).obj M) W').hom =
      (ModuleCat.extendScalars φ.hom).map (factorPullbackSectionsIso f M W).hom ≫
        scalarSectionsBaseChangeMap φ (W.ι ≫ f) (W'.ι ≫ f') k
          (square_restrict_comm φ f f' g w W.ι W'.ι k sq)
          ((Scheme.Modules.pullback W.ι).obj M) ≫
        (relativeGlobalSections (W'.ι ≫ f')).map
          ((pullbackSquareIso g W.ι W'.ι k sq).hom.app M) := by
  apply ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  simp only [scalarFactorSectionsMap, scalarSectionsBaseChangeMap, Equiv.apply_symm_apply]
  exact factorSectionsMap_pullbackUnit_comp g M hW φ f f' w k sq

/-- In a Cartesian affine restricted square, the actual scalar factor map is invertible. -/
lemma isIso_scalarFactorSectionsMap_pullbackUnit_of_isPullback
    [IsAffine (W : Scheme)] [IsAffine (W' : Scheme)] [M.IsQuasicoherent]
    (k : (W' : Scheme) ⟶ (W : Scheme)) (sq : k ≫ W.ι = W'.ι ≫ g)
    (h : IsPullback k (W'.ι ≫ f') (W.ι ≫ f) (Spec.map φ)) :
    IsIso (scalarFactorSectionsMap φ f f' g w
      ((pullbackPushforwardAdjunction g).unit.app M) hW) := by
  have : ((Scheme.Modules.pullback W.ι).obj M).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (W : Scheme).ringCatSheaf).prop_of_iso
      ((restrictFunctorIsoPullback W.ι).app M) inferInstance
  have := isIso_scalarSectionsBaseChangeMap_of_isPullback_affine φ (W.ι ≫ f) (W'.ι ≫ f') k
    (square_restrict_comm φ f f' g w W.ι W'.ι k sq) h ((Scheme.Modules.pullback W.ι).obj M)
  have : IsIso (scalarFactorSectionsMap φ f f' g w
      ((pullbackPushforwardAdjunction g).unit.app M) hW ≫
        (factorPullbackSectionsIso f' ((Scheme.Modules.pullback g).obj M) W').hom) := by
    rw [scalarFactorSectionsMap_pullbackUnit_comp g M hW φ f f' w k sq]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (factorPullbackSectionsIso f' ((Scheme.Modules.pullback g).obj M) W').hom

/-- The square restricted to a full inverse-image open remains Cartesian. -/
lemma isPullback_resLE_baseChange (h : IsPullback g f' f (Spec.map φ))
    (he : W' = g ⁻¹ᵁ W) :
    IsPullback (g.resLE W W' hW) (W'.ι ≫ f') (W.ι ≫ f) (Spec.map φ) := by
  subst W'
  have ht : IsPullback (g.resLE W (g ⁻¹ᵁ W) hW) (g ⁻¹ᵁ W).ι W.ι g := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using isPullback_morphismRestrict g W
  exact ht.paste_vert h

section Cover

variable [IsAffineHom g] (𝒰 : X.OrderedAffineCover)

/-- Affineness of the cover intersections suffices to make every actual factor map invertible. -/
lemma isIso_scalarFactorSectionsMap_inverseImageCover [M.IsQuasicoherent]
    (h : IsPullback g f' f (Spec.map φ))
    (p : ℕ) (s : 𝒰.Idx p) (ha : IsAffineOpen (𝒰.inter s)) :
    IsIso (scalarFactorSectionsMap φ f f' g w
      ((pullbackPushforwardAdjunction g).unit.app M) (inverseImageCover_inter_le g 𝒰 s)) := by
  let W := 𝒰.inter s
  let W' := (inverseImageCover g 𝒰).inter s
  have he : W' = g ⁻¹ᵁ W := inverseImageCover_inter g 𝒰 s
  have : IsAffine (W : Scheme) := ha
  have : IsAffine (W' : Scheme) := by
    change IsAffineOpen W'
    rw [he]
    exact ha.preimage g
  let hW := inverseImageCover_inter_le g 𝒰 s
  exact isIso_scalarFactorSectionsMap_pullbackUnit_of_isPullback g M hW φ f f' w
    (g.resLE W W' hW) (g.resLE_comp_ι hW)
    (isPullback_resLE_baseChange g hW φ f f' h he)

/-- The actual Čech scalar sections map is an isomorphism for a Cartesian square,
provided the ordered cover has affine intersections. -/
lemma isIso_scalarCechSectionsMap_of_isPullback [M.IsQuasicoherent]
    (h : IsPullback g f' f (Spec.map φ))
    (ha : ∀ (p : ℕ) (s : 𝒰.Idx p), IsAffineOpen (𝒰.inter s)) :
    IsIso (scalarCechSectionsMap φ f f' g w
      ((pullbackPushforwardAdjunction g).unit.app M) 𝒰) :=
  isIso_scalarCechSectionsMap_of_factors φ f f' g w
    ((pullbackPushforwardAdjunction g).unit.app M) 𝒰
    (fun p s => isIso_scalarFactorSectionsMap_inverseImageCover g M φ f f' w 𝒰 h p s (ha p s))

/-- The actual Cartesian Čech scalar map is a quasi-isomorphism. -/
lemma quasiIso_scalarCechSectionsMap_of_isPullback [M.IsQuasicoherent]
    (h : IsPullback g f' f (Spec.map φ))
    (ha : ∀ (p : ℕ) (s : 𝒰.Idx p), IsAffineOpen (𝒰.inter s)) :
    QuasiIso (scalarCechSectionsMap φ f f' g w
      ((pullbackPushforwardAdjunction g).unit.app M) 𝒰) := by
  let := isIso_scalarCechSectionsMap_of_isPullback g M φ f f' w 𝒰 h ha
  infer_instance

/-- A separated scheme has affine ordered-cover intersections. -/
lemma isAffineOpen_inter_of_isSeparated [X.IsSeparated]
    (p : ℕ) (s : 𝒰.Idx p) : IsAffineOpen (𝒰.inter s) :=
  IsAffineOpen.iInf (fun j => 𝒰.isAffineOpen (s.1 j))

/-- Separatedness over the affine base supplies the affine-intersection hypothesis. -/
lemma isIso_scalarCechSectionsMap_of_isPullback_of_isSeparated
    [IsSeparated f] [M.IsQuasicoherent]
    (h : IsPullback g f' f (Spec.map φ)) :
    IsIso (scalarCechSectionsMap φ f f' g w
      ((pullbackPushforwardAdjunction g).unit.app M) 𝒰) := by
  let : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  exact isIso_scalarCechSectionsMap_of_isPullback g M φ f f' w 𝒰 h
    (isAffineOpen_inter_of_isSeparated 𝒰)

/-- The separated Cartesian comparison also has the required quasi-isomorphism instance. -/
lemma quasiIso_scalarCechSectionsMap_of_isPullback_of_isSeparated
    [IsSeparated f] [M.IsQuasicoherent]
    (h : IsPullback g f' f (Spec.map φ)) :
    QuasiIso (scalarCechSectionsMap φ f f' g w
      ((pullbackPushforwardAdjunction g).unit.app M) 𝒰) := by
  let := isIso_scalarCechSectionsMap_of_isPullback_of_isSeparated g M φ f f' w 𝒰 h
  infer_instance

end Cover

end Langlands.AlgebraicGeometry.Modules.CechResolution
