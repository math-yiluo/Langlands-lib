import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelParameterIsomorphism
import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevelParameterGeometry
import Langlands.AbelianScheme.PolarizedFiniteLevel.TorsionDetection
import Mathlib.CategoryTheory.Endomorphism

/-! # Actual automorphism action and fixed full-level parameters -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S : Scheme.{u}} {A B : AbelianScheme S} (g n : ℕ)

/-- The actual action of family automorphisms on the full-level parameter
as a homomorphism of automorphism groups. -/
def fullLevelParameterAut (A : AbelianScheme S)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) :
    Aut A →* Aut (fullLevelParameterScheme A g n hn hunit) where
  toFun := fullLevelParameterIso g n hn hunit
  map_one' := fullLevelParameterIso_refl g n hn hunit
  map_mul' e d := fullLevelParameterIso_trans g n hn hunit d e

private theorem fullLevel_sections_injective :
    Function.Injective (FullLevel.sections (A := A) (g := g) (n := n)) := by
  intro v w h
  cases v
  cases w
  cases h
  rfl

/-- A parameter map is fixed precisely when its classified prescribed ordered
sections are fixed by the actual pulled-back family automorphism. -/
theorem fullLevelParameterIso_fixed_iff
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (e : A ≅ A) (T : Over S)
    (f : T ⟶ fullLevelParameterScheme A g n hn hunit) :
    f ≫ (fullLevelParameterIso g n hn hunit e).hom = f ↔
      mapTuple ((baseChange T.hom).mapIso e).hom
        (fullLevelParameterHomEquiv A g n hn hunit T f).sections =
        (fullLevelParameterHomEquiv A g n hn hunit T f).sections := by
  constructor
  · intro h
    rw [← fullLevelParameterIso_hom_sections, h]
  · intro h
    apply (fullLevelParameterHomEquiv A g n hn hunit T).injective
    apply fullLevel_sections_injective g n
    rw [fullLevelParameterIso_hom_sections, h]

/-- For a supplied full level, equality on the ordered tuple is equivalent to
equality of the actual induced torsion-scheme maps. -/
theorem FullLevel.mapTuple_eq_iff_torsionMap_eq (v : FullLevel A g n)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (f k : A ⟶ B) :
    mapTuple f v.sections = mapTuple k v.sections ↔
      kernelLevelMap (groupHom f) n = kernelLevelMap (groupHom k) n := by
  constructor
  · intro h
    exact v.torsionMap_ext hn hunit (congrFun h)
  · intro h
    funext i
    let x := (kernelLevelEquiv A.toGrp (Over.mk (𝟙 S)) n).symm (v.sections i)
    have hf := kernelLevelEquiv_map (Over.mk (𝟙 S)) (groupHom f) n x
    have hk := kernelLevelEquiv_map (Over.mk (𝟙 S)) (groupHom k) n x
    dsimp only [x] at hf hk
    simp only [AddEquiv.apply_symm_apply] at hf hk
    change levelMap (Over.mk (𝟙 S)) (groupHom f) n (v.sections i) =
      levelMap (Over.mk (𝟙 S)) (groupHom k) n (v.sections i)
    rw [← hf, ← hk, h]

private theorem mapTuple_identity (v : SectionTuple A g n) :
    mapTuple (𝟙 A) v = v := by
  funext i
  apply toSection_injective A.toGrp (Over.mk (𝟙 S)) n
  exact Category.comp_id (Additive.toMul (v i)).val

private theorem kernelLevelMap_identity :
    kernelLevelMap (groupHom (𝟙 A)) n = 𝟙 _ := by
  apply (cancel_mono (GroupScheme.kernelι
    (GroupScheme.multiplication A.toGrp (n : ℤ))).hom.hom).mp
  rw [kernelLevelMap_ι]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Fixed parameter maps are exactly those for which the pulled-back family
automorphism is the identity on the actual torsion scheme. -/
theorem fullLevelParameterIso_fixed_iff_torsion
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤)))
    (e : A ≅ A) (T : Over S)
    (f : T ⟶ fullLevelParameterScheme A g n hn hunit) :
    f ≫ (fullLevelParameterIso g n hn hunit e).hom = f ↔
      kernelLevelMap (groupHom ((baseChange T.hom).mapIso e).hom) n = 𝟙 _ := by
  rw [fullLevelParameterIso_fixed_iff]
  let v := fullLevelParameterHomEquiv A g n hn hunit T f
  change mapTuple ((baseChange T.hom).mapIso e).hom v.sections = v.sections ↔ _
  simpa only [mapTuple_identity, kernelLevelMap_identity] using
    (FullLevel.mapTuple_eq_iff_torsionMap_eq g n v hn
      (Tate.isUnit_natCast_pullback T.hom n hunit)
      ((baseChange T.hom).mapIso e).hom (𝟙 _))

/-- The actual fixed-parameter scheme over the original base. -/
def fullLevelParameterFixedScheme (A : AbelianScheme S)
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (e : A ≅ A) : Over S :=
  equalizer (fullLevelParameterIso g n hn hunit e).hom (𝟙 _)

/-- The actual inclusion of fixed full-level parameters. -/
def fullLevelParameterFixedInclusion
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (e : A ≅ A) :
    fullLevelParameterFixedScheme g n A hn hunit e ⟶
      fullLevelParameterScheme A g n hn hunit :=
  equalizer.ι _ _

/-- Maps into the actual fixed scheme are fixed maps into the parameter scheme. -/
def fullLevelParameterFixedHomMapEquiv
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (e : A ≅ A) (T : Over S) :
    (T ⟶ fullLevelParameterFixedScheme g n A hn hunit e) ≃
      {f : T ⟶ fullLevelParameterScheme A g n hn hunit //
        f ≫ (fullLevelParameterIso g n hn hunit e).hom = f} where
  toFun f := ⟨f ≫ fullLevelParameterFixedInclusion g n hn hunit e, by
    change (f ≫ equalizer.ι _ _) ≫ _ = _
    rw [Category.assoc, equalizer.condition, Category.comp_id]
    rfl⟩
  invFun f := equalizer.lift f.val (by simpa only [Category.comp_id] using f.property)
  left_inv f := by
    apply equalizer.hom_ext
    exact equalizer.lift_ι _ _
  right_inv f := by
    apply Subtype.ext
    exact equalizer.lift_ι _ _

/-- The fixed-parameter scheme classifies exactly the full levels whose
prescribed ordered sections are fixed by the pulled-back automorphism. -/
def fullLevelParameterFixedHomEquiv
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (e : A ≅ A) (T : Over S) :
    (T ⟶ fullLevelParameterFixedScheme g n A hn hunit e) ≃
      {v : FullLevel ((baseChange T.hom).obj A) g n //
        mapTuple ((baseChange T.hom).mapIso e).hom v.sections = v.sections} :=
  (fullLevelParameterFixedHomMapEquiv g n hn hunit e T).trans
    ((fullLevelParameterHomEquiv A g n hn hunit T).subtypeEquiv
      (fun f => fullLevelParameterIso_fixed_iff g n hn hunit e T f))

/-- The actual inclusion of fixed parameters is an open immersion. -/
theorem fullLevelParameterFixedInclusion_isOpenImmersion
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (e : A ≅ A) :
    IsOpenImmersion (fullLevelParameterFixedInclusion g n hn hunit e).left := by
  have : Etale (fullLevelParameterScheme A g n hn hunit).hom :=
    (fullLevelParameterScheme_finiteEtale A g n hn hunit).2
  change IsOpenImmersion (equalizer.ι
    (fullLevelParameterIso g n hn hunit e).hom (𝟙 _)).left
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod _ _).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsOpenImmersion _
    (Over.prodLeftIsoPullback _ _).hom]
  convert! (inferInstance : IsOpenImmersion
    (pullback.diagonal (fullLevelParameterScheme A g n hn hunit).hom))
  ext1 <;> simp [← Over.comp_left]

/-- The actual inclusion of fixed parameters is also a closed immersion. -/
theorem fullLevelParameterFixedInclusion_isClosedImmersion
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (e : A ≅ A) :
    IsClosedImmersion (fullLevelParameterFixedInclusion g n hn hunit e).left := by
  have : IsFinite (fullLevelParameterScheme A g n hn hunit).hom :=
    (fullLevelParameterScheme_finiteEtale A g n hn hunit).1
  change IsClosedImmersion (equalizer.ι
    (fullLevelParameterIso g n hn hunit e).hom (𝟙 _)).left
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod _ _).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (Over.prodLeftIsoPullback _ _).hom]
  convert! (inferInstance : IsClosedImmersion
    (pullback.diagonal (fullLevelParameterScheme A g n hn hunit).hom))
  ext1 <;> simp [← Over.comp_left]

/-- Fixed full-level parameters form a finite étale scheme over the base. -/
theorem fullLevelParameterFixedScheme_finiteEtale
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (e : A ≅ A) :
    IsFinite (fullLevelParameterFixedScheme g n A hn hunit e).hom ∧
      Etale (fullLevelParameterFixedScheme g n A hn hunit e).hom := by
  obtain ⟨hfin, het⟩ := fullLevelParameterScheme_finiteEtale A g n hn hunit
  have : IsFinite (fullLevelParameterScheme A g n hn hunit).hom := hfin
  have : Etale (fullLevelParameterScheme A g n hn hunit).hom := het
  have : IsOpenImmersion (fullLevelParameterFixedInclusion g n hn hunit e).left :=
    fullLevelParameterFixedInclusion_isOpenImmersion g n hn hunit e
  have : IsClosedImmersion (fullLevelParameterFixedInclusion g n hn hunit e).left :=
    fullLevelParameterFixedInclusion_isClosedImmersion g n hn hunit e
  rw [← (fullLevelParameterFixedInclusion g n hn hunit e).w]
  constructor <;> infer_instance

/-- The actual fixed full-level parameter as a finite étale cover of the base. -/
def fullLevelParameterFixedFiniteEtaleCover
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (e : A ≅ A) :
    Langlands.AlgebraicGeometry.FiniteEtale.Cover S :=
  ⟨fullLevelParameterFixedScheme g n A hn hunit e,
    fullLevelParameterFixedScheme_finiteEtale g n hn hunit e⟩

/-- Forgetting finite étaleness recovers the actual equalizer scheme. -/
@[simp]
theorem fullLevelParameterFixedFiniteEtaleCover_obj
    (hn : 0 < n) (hunit : IsUnit (n : Γ(S, ⊤))) (e : A ≅ A) :
    (fullLevelParameterFixedFiniteEtaleCover g n hn hunit e).obj =
      fullLevelParameterFixedScheme g n A hn hunit e :=
  rfl

end Langlands.AbelianScheme.PolarizedFiniteLevel
