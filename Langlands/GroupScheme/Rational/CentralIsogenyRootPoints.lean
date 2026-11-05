import Langlands.GroupScheme.Dynamic.CentralIsogenyUnipotentPoints
import Langlands.GroupScheme.Dynamic.ActionStability
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Rational.RootSubgroupPositive
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Langlands.GroupScheme.Rational.WeightVectorUniqueness

/-! # Rational relative root points under a central isogeny -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section ArbitraryBase

variable {B : Scheme.{u}} {S : CommGroupScheme B} {C G : GroupScheme B}
    (q : C ⟶ G) (i : S.toGrp ⟶ C) (a : characterLattice S)

/-- The restriction of the actual point map to relative root subgroups. -/
def rootPointsMap (T : Over B) :
    (subgroup i a).carrier T →* (subgroup (i ≫ q) a).carrier T where
  toFun g := ⟨(g : T ⟶ C.X) ≫ q.hom.hom, comp_mem_subgroup i a q g.2⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' _g _h := Subtype.ext (MonObj.mul_comp _ _ _)

@[simp] theorem rootPointsMap_coe (T : Over B) (g : (subgroup i a).carrier T) :
    (rootPointsMap q i a T g : T ⟶ G.X) = (g : T ⟶ C.X) ≫ q.hom.hom := rfl

/-- A positive-power restriction of a root orbit has the same zero limit. -/
theorem IsOrbitExtension.hasLimit_of_power (ν : Gm B ⟶ S) {m : ℕ} (hm : 0 < m)
    (hcomp : ν ≫ a = Gm.powerHom B (m : ℤ))
    {T : Over B} {g : T ⟶ C.X} {e : T ⊗ AffineLine.scheme B ⟶ C.X}
    (he : IsOrbitExtension i a g e) :
    Dynamic.HasLimit (CommGroupScheme.groupHom ν ≫ i) g (Dynamic.evalZero e) := by
  refine ⟨T ◁ AffineLine.powerMap B m ≫ e, ?_,
    AffineLine.evalZero_whiskerLeft_powerMap B hm e⟩
  rw [Dynamic.IsOrbitExtension]
  calc
    T ◁ AffineLine.unitInclusion B ≫ (T ◁ AffineLine.powerMap B m ≫ e) =
        T ◁ (AffineLine.unitInclusion B ≫ AffineLine.powerMap B m) ≫ e := by
          rw [whiskerLeft_comp, Category.assoc]
    _ = T ◁ ((CommGroupScheme.groupHom (ν ≫ a)).hom.hom ≫
        AffineLine.unitInclusion B) ≫ e := by
          rw [hcomp, AffineLine.unitInclusion_comp_powerMap]
    _ = T ◁ (CommGroupScheme.groupHom ν).hom.hom ≫
        (T ◁ ((CommGroupScheme.groupHom a).hom.hom ≫
          AffineLine.unitInclusion B) ≫ e) := by
            rw [← Category.assoc, ← whiskerLeft_comp]
            rfl
    _ = T ◁ (CommGroupScheme.groupHom ν).hom.hom ≫ orbit i g :=
      congrArg (T ◁ (CommGroupScheme.groupHom ν).hom.hom ≫ ·) he
    _ = Dynamic.orbit (CommGroupScheme.groupHom ν ≫ i) g :=
      orbit_comp_cocharacter i _ g

private theorem orbit_mem_dynamicUnipotent
    (ν : (Gm B).toGrp ⟶ S.toGrp) {T V : Over B} {g : T ⟶ C.X}
    (hg : g ∈ (Dynamic.unipotent (ν ≫ i)).carrier T) (b : V ⟶ T ⊗ S.X) :
    b ≫ orbit i g ∈ (Dynamic.unipotent (ν ≫ i)).carrier V := by
  rw [orbit, AutomorphicAction.naturality]
  exact Dynamic.unipotent_isStable_conjugation i ν V (b ≫ snd T S.X)
    (b ≫ fst T S.X ≫ g) ((Dynamic.unipotent (ν ≫ i)).comp_mem (b ≫ fst T S.X) hg)

private theorem exists_desc_over {X Y Z : Over B} (π : X ⟶ Y)
    [EffectiveEpi π.left] (f : X ⟶ Z)
    (hf : ∀ (V : Over B) (b b' : V ⟶ X), b ≫ π = b' ≫ π → b ≫ f = b' ≫ f) :
    ∃ d : Y ⟶ Z, π ≫ d = f := by
  have h : ∀ {V : Scheme.{u}} (b b' : V ⟶ X.left), b ≫ π.left = b' ≫ π.left →
      b ≫ f.left = b' ≫ f.left := by
    intro V b b' hb
    let W : Over B := Over.mk (b ≫ X.hom)
    have hb' : b' ≫ X.hom = b ≫ X.hom := by
      rw [← Over.w π, ← Category.assoc, ← Category.assoc, hb]
    let c : W ⟶ X := Over.homMk b rfl
    let c' : W ⟶ X := Over.homMk b' hb'
    exact congrArg (fun e => e.left) (hf W c c' (Over.OverMorphism.ext hb))
  refine ⟨Over.homMk (EffectiveEpi.desc π.left f.left h) ?_, ?_⟩
  · rw [← cancel_epi π.left, EffectiveEpi.fac_assoc]
    simp
  · ext
    exact EffectiveEpi.fac _ _ h

private abbrev fpqcProperty : MorphismProperty Scheme.{u} :=
  @QuasiCompact ⊓ (@Flat ⊓ @Surjective)

set_option backward.isDefEq.respectTransparency false in
private theorem effectiveEpi_whiskerLeft_character
    [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
    [Flat (CommGroupScheme.groupHom a).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom a).hom.hom.left] (T : Over B) :
    EffectiveEpi (T ◁ (CommGroupScheme.groupHom a).hom.hom).left := by
  have hp : fpqcProperty (T ◁ (CommGroupScheme.groupHom a).hom.hom).left := by
    exact MorphismProperty.pullbackMap (P := fpqcProperty)
      (by change fpqcProperty (𝟙 T.left); exact ⟨inferInstance, inferInstance, inferInstance⟩)
      ⟨inferInstance, inferInstance, inferInstance⟩
      (by simp) (Over.w (CommGroupScheme.groupHom a).hom.hom).symm
  obtain ⟨hqc, hf, hs⟩ := hp
  let : QuasiCompact (T ◁ (CommGroupScheme.groupHom a).hom.hom).left := hqc
  let : Flat (T ◁ (CommGroupScheme.groupHom a).hom.hom).left := hf
  let : Surjective (T ◁ (CommGroupScheme.groupHom a).hom.hom).left := hs
  infer_instance

private theorem exists_punctured_orbit_lift [IsSeparated C.X.hom]
    [QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left]
    [Flat (CommGroupScheme.groupHom a).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom a).hom.hom.left]
    (hq : IsCentral (kernelι q)) (ν : (Gm B).toGrp ⟶ S.toGrp)
    {T : Over B} {g : T ⟶ C.X}
    (hg : g ∈ (Dynamic.unipotent (ν ≫ i)).carrier T)
    {e : T ⊗ AffineLine.scheme B ⟶ G.X}
    (he : IsOrbitExtension (i ≫ q) a (g ≫ q.hom.hom) e) :
    ∃ c : T ⊗ (Gm B).X ⟶ C.X,
      T ◁ (CommGroupScheme.groupHom a).hom.hom ≫ c = orbit i g ∧
      c ≫ q.hom.hom = T ◁ AffineLine.unitInclusion B ≫ e := by
  let π := T ◁ (CommGroupScheme.groupHom a).hom.hom
  have : EffectiveEpi π.left := effectiveEpi_whiskerLeft_character a T
  have : Epi π := Over.epi_of_epi_left π
  have horb : orbit i g ≫ q.hom.hom = π ≫ (T ◁ AffineLine.unitInclusion B ≫ e) := by
    rw [← orbit_comp_hom, ← he]
    simp only [π, whiskerLeft_comp, Category.assoc]
  obtain ⟨c, hc⟩ := exists_desc_over π (orbit i g) (by
    intro V b b' hb
    have hb_mem := orbit_mem_dynamicUnipotent i ν hg b
    have hb'_mem := orbit_mem_dynamicUnipotent i ν hg b'
    have heq : Dynamic.unipotentPointsMap q (ν ≫ i) V ⟨b ≫ orbit i g, hb_mem⟩ =
        Dynamic.unipotentPointsMap q (ν ≫ i) V ⟨b' ≫ orbit i g, hb'_mem⟩ := by
      apply Subtype.ext
      change (b ≫ orbit i g) ≫ q.hom.hom = (b' ≫ orbit i g) ≫ q.hom.hom
      rw [Category.assoc, Category.assoc, horb, ← Category.assoc b,
        ← Category.assoc b', hb]
    exact congrArg Subtype.val
      (Dynamic.unipotentPointsMap_injective q (ν ≫ i) hq V heq))
  refine ⟨c, hc, ?_⟩
  apply (cancel_epi π).mp
  rw [← Category.assoc, hc, horb]

end ArbitraryBase

section Field

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {C G : GroupScheme (Spec (CommRingCat.of k))}
    (q : C ⟶ G) (i : S.toGrp ⟶ C) (a : characterLattice S)

/-- A full central kernel is injective on nonzero split-character root subgroups,
including points over every test scheme. -/
theorem rootPointsMap_injective [IsSeparated C.X.hom]
    (hq : IsCentral (kernelι q)) (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) (T : Over _) :
    Function.Injective (rootPointsMap q i a T) := by
  obtain ⟨m, hm, ν, hν⟩ := hS.exists_pairing_eq_pos ha
  have hp : 0 < latticePairing S a ν := by rw [hν]; exact_mod_cast hm
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Subtype.ext
  exact Dynamic.eq_one_of_mem_unipotent_of_comp_eq_one q
    (CommGroupScheme.groupHom ν ≫ i) hq
    (subgroup_le_dynamicUnipotent i ν hp T g.2) (congrArg Subtype.val hg)

variable [C.X.left.IsSeparated] [G.X.left.IsSeparated]

/-- Rational points of a nonzero split-character root subgroup lift through an
actual central isogeny to the corresponding source root subgroup. -/
theorem exists_root_lift (hq : IsCentralIsogeny q)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hg : g ∈ (subgroup (i ≫ q) a).carrier (Over.mk (𝟙 _))) :
    ∃ g' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X,
      g' ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) ∧ g' ≫ q.hom.hom = g := by
  obtain ⟨m, hm, ν, hν⟩ := hS.exists_pairing_eq_pos ha
  have hp : 0 < latticePairing S a ν := by rw [hν]; exact_mod_cast hm
  obtain ⟨hqc, hf, hs⟩ := characterFpqc k S hS a ha
  let : QuasiCompact (CommGroupScheme.groupHom a).hom.hom.left := hqc
  let : Flat (CommGroupScheme.groupHom a).hom.hom.left := hf
  let : Surjective (CommGroupScheme.groupHom a).hom.hom.left := hs
  have : IsFinite q.hom.hom.left := hq.isFinite
  have hgu : g ∈ (Dynamic.unipotent ((CommGroupScheme.groupHom ν ≫ i) ≫ q)).carrier
      (Over.mk (𝟙 _)) := by
    rw [Category.assoc]
    exact subgroup_le_dynamicUnipotent (i ≫ q) ν hp _ hg
  obtain ⟨x, hx, hxq⟩ := Dynamic.exists_unipotent_lift q hq
    (CommGroupScheme.groupHom ν ≫ i) g hgu
  obtain ⟨e, he, _he0⟩ := hg
  have heq : IsOrbitExtension (i ≫ q) a (x ≫ q.hom.hom) e := by rw [hxq]; exact he
  obtain ⟨c, hc, hcq⟩ := exists_punctured_orbit_lift q i a hq.isCentral_kernelι
    (CommGroupScheme.groupHom ν) hx heq
  obtain ⟨e', he'unit, _he'q⟩ := AffineLine.exists_base_lift_of_isProper q.hom.hom e c hcq
  have he' : IsOrbitExtension i a x e' := by
    rw [IsOrbitExtension, whiskerLeft_comp, Category.assoc, he'unit, hc]
  have hcomp : ν ≫ a = Gm.powerHom (Spec (CommRingCat.of k)) (m : ℤ) := by
    change ν ≫ a = (m : ℤ) • 𝟙 (Gm _)
    rw [← hν]
    exact eq_gmEndEquiv_zsmul k (ν ≫ a)
  refine ⟨x, ⟨e', he', ?_⟩, hxq⟩
  exact (he'.hasLimit_of_power i a ν hm hcomp).unique
    (CommGroupScheme.groupHom ν ≫ i) hx

/-- The actual point map is surjective on rational nonzero split-character root points. -/
theorem rootPointsMap_surjective (hq : IsCentralIsogeny q)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) :
    Function.Surjective (rootPointsMap q i a (Over.mk (𝟙 _))) := by
  intro g
  obtain ⟨x, hx, hxq⟩ := exists_root_lift q i a hq hS ha g g.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩

/-- The actual central isogeny identifies rational relative root subgroups for a
supplied split acting torus and a nonzero character. -/
def centralIsogenyRootPointsEquiv (hq : IsCentralIsogeny q)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) :
    (subgroup i a).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≃*
      (subgroup (i ≫ q) a).carrier (Over.mk (𝟙 _)) :=
  MulEquiv.ofBijective (rootPointsMap q i a (Over.mk (𝟙 _)))
    ⟨rootPointsMap_injective q i a hq.isCentral_kernelι hS ha _,
      rootPointsMap_surjective q i a hq hS ha⟩

@[simp] theorem centralIsogenyRootPointsEquiv_coe (hq : IsCentralIsogeny q)
    (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (g : (subgroup i a).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    (centralIsogenyRootPointsEquiv q i a hq hS ha g :
      Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) =
      (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X) ≫ q.hom.hom := rfl

end Field

end Langlands.GroupScheme.RelativeRoot
