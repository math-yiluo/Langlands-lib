import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOneLocalFramesStatement
import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateCoverProof
import Langlands.AlgebraicGeometry.Picard.LineBundleDescent

/-! # Proof: coordinate frames and local rank one of `𝒪(1)` on projective space -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

universe u

namespace ProjTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- At a point outside `V(f)`, the fraction `f / 1` is a unit of the localization. -/
lemma isUnit_mk_one {f : A} (x : ProjectiveSpectrum 𝒜) (hfx : f ∉ x.asHomogeneousIdeal) :
    IsUnit (Localization.mk f 1 : Localizations 𝒜 x) := by
  rw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.map_units (Localizations 𝒜 x)
    (⟨f, hfx⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)

/-- Multiplication by `f / 1` is injective on the homogeneous localization at a point outside
`V(f)`. -/
lemma val_mul_mk_one_injective {f : A} (x : ProjectiveSpectrum 𝒜)
    (hfx : f ∉ x.asHomogeneousIdeal)
    {y z : HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal}
    (h : y.val * Localization.mk f 1 = z.val * Localization.mk f 1) : y = z :=
  HomogeneousLocalization.val_injective _ ((isUnit_mk_one x hfx).mul_left_injective h)

/-- The degree-zero fraction `a / (b f)` times `f / 1` is `a / b`. -/
lemma val_mk_mul_mk_one {d j : ℕ} {f : A} (hf : f ∈ 𝒜 d) (x : ProjectiveSpectrum 𝒜)
    {a b : A} (ha : a ∈ 𝒜 (j + d)) (hb : b ∈ 𝒜 j)
    (hbf : b * f ∈ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (hbx : b ∈ x.asHomogeneousIdeal.toIdeal.primeCompl) :
    (HomogeneousLocalization.mk
        ⟨j + d, ⟨a, ha⟩, ⟨b * f, SetLike.mul_mem_graded hb hf⟩, hbf⟩ :
        HomogeneousLocalization.AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal).val *
      Localization.mk f 1 = Localization.mk a ⟨b, hbx⟩ := by
  rw [HomogeneousLocalization.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one]; ring⟩

/-- For a section `t` of `𝒪(d)` over an open inside `D₊(f)`, with `f` of degree `d`, the value
of `t` at each point is `f / 1` times an element of the homogeneous localization. -/
lemma exists_val_mul_eq {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (t : (sectionsInType 𝒜 d).1.obj (op W))
    (x : W) :
    ∃ y : HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal,
      y.val * Localization.mk f 1 = t.1 x := by
  obtain ⟨V, hxV, iVW, j, ⟨a, ha⟩, ⟨b, hb⟩, nb, w⟩ := t.2 x
  have hfx : f ∉ x.1.asHomogeneousIdeal := hW x.2
  have hbx : b ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl := nb ⟨x.1, hxV⟩
  have hbf : b * f ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl :=
    x.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem hbx hfx
  refine ⟨_, (val_mk_mul_mk_one hf x.1 ha hb hbf hbx).trans ?_⟩
  exact (w ⟨x.1, hxV⟩).symm

/-- Division by the section `f / 1`: a section of `𝒪(d)` over an open inside `D₊(f)` gives a
section of the structure sheaf of `Proj`. -/
def divBySection {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (t : (sectionsInType 𝒜 d).1.obj (op W)) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op W) :=
  ⟨fun x => (exists_val_mul_eq hf hW t x).choose, fun x => by
    obtain ⟨V, hxV, iVW, j, ⟨a, ha⟩, ⟨b, hb⟩, nb, w⟩ := t.2 x
    have hbf : ∀ y : V, b * f ∈ y.1.asHomogeneousIdeal.toIdeal.primeCompl := fun y =>
      y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (nb y) (hW (iVW.le y.2))
    refine ⟨V, hxV, iVW, j + d, ⟨a, ha⟩, ⟨b * f, SetLike.mul_mem_graded hb hf⟩, hbf,
      fun y => ?_⟩
    have hfy : f ∉ y.1.asHomogeneousIdeal := hW (iVW.le y.2)
    apply val_mul_mk_one_injective y.1 hfy
    refine ((exists_val_mul_eq hf hW t (iVW y)).choose_spec.trans (w y)).trans ?_
    exact (val_mk_mul_mk_one hf y.1 ha hb (hbf y) (nb y)).symm⟩

/-- On an open `W ≤ D₊(f)`, with `f` of degree `d`, multiplication of structure-sheaf sections
by the restriction of the section `f / 1` of `𝒪(d)` is a bijection onto the sections of
`𝒪(d)`. -/
lemma bijective_smul_restrict_section {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) {W : (Proj 𝒜).Opens}
    (hW : W ≤ Proj.basicOpen 𝒜 f) :
    Function.Bijective fun g : Γ(Proj 𝒜, W) =>
      g • (projTwistingSheaf 𝒜 d).presheaf.map (homOfLE le_top : W ⟶ ⊤).op
        (projTwistingSheafSection 𝒜 d f hf) := by
  refine ⟨fun g h e => ?_, fun t => ⟨divBySection hf hW t, ?_⟩⟩
  · have e' : ∀ x : W, (g.1 x).val * Localization.mk f 1 = (h.1 x).val * Localization.mk f 1 :=
      fun x => congrFun (congrArg Subtype.val e) x
    exact Subtype.ext (funext fun x => val_mul_mk_one_injective x.1 (hW x.2) (e' x))
  · exact Subtype.ext (funext fun x => (exists_val_mul_eq hf hW t x).choose_spec)

end ProjTwist

namespace ProjTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- For `f` homogeneous of degree `d`, the section `f / 1` of `𝒪(d)` trivializes `𝒪(d)` on
every open `U ≤ D₊(f)`. -/
lemma trivializesOn_projTwistingSheafSection {d : ℕ} {f : A} (hf : f ∈ 𝒜 d)
    {U : (Proj 𝒜).Opens} (hU : U ≤ Proj.basicOpen 𝒜 f) :
    Langlands.SchemeModule.TrivializesOn (projTwistingSheaf 𝒜 d)
      (projTwistingSheafSection 𝒜 d f hf) U := by
  unfold Langlands.SchemeModule.TrivializesOn
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  have hV : U.ι ''ᵁ V ≤ Proj.basicOpen 𝒜 f := (U.ι_image_le V).trans hU
  have e : ∀ g : Γ(Proj 𝒜, U.ι ''ᵁ V),
      (((Scheme.Modules.restrictFunctor U.ι).map
        (Langlands.SchemeModule.sectionHom _ (projTwistingSheafSection 𝒜 d f hf))).app V) g =
      g • (projTwistingSheaf 𝒜 d).presheaf.map (homOfLE le_top : U.ι ''ᵁ V ⟶ ⊤).op
        (projTwistingSheafSection 𝒜 d f hf) :=
    fun g => Langlands.SchemeModule.LineBundleDescent.sectionHom_app _ _ _ g
  rw [show ⇑(((Scheme.Modules.restrictFunctor U.ι).map
      (Langlands.SchemeModule.sectionHom _ (projTwistingSheafSection 𝒜 d f hf))).app V) = _
    from funext e]
  exact bijective_smul_restrict_section hf hV

end ProjTwist

/-- Once the coordinate sections are frames on their coordinate opens, the published coordinate
cover makes `𝒪(1)` locally free of rank one. (Contributed by Worker 311.) -/
lemma isLocallyFreeRankOne_twistOne_of_coordinateFrames
    (R : Type u) [CommRing R] (n : ℕ)
    (h : ∀ i : Fin (n + 1),
      Langlands.SchemeModule.TrivializesOn (twistOne R n)
        (twistOneCoordinate R n i) (projectiveSpaceCoordinateOpen R n i)) :
    Picard.IsLocallyFreeRankOne (twistOne R n) := by
  intro x
  have hx : x ∈ ⨆ i : Fin (n + 1), projectiveSpaceCoordinateOpen R n i := by
    rw [(projectiveSpaceCoordinateCover R n).2.1]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let U := projectiveSpaceCoordinateOpen R n i
  let φ := (Scheme.Modules.restrictFunctor U.ι).map
    (Langlands.SchemeModule.sectionHom (twistOne R n) (twistOneCoordinate R n i))
  have : IsIso φ := h i
  exact ⟨U, hi, ⟨(asIso φ).symm ≪≫ Scheme.Modules.restrictUnitIso U.ι⟩⟩

/-- On projective space, each coordinate section `X i` of `𝒪(1)` trivializes `𝒪(1)` on the
coordinate open `D₊(X i)`, and `𝒪(1)` is locally free of rank one. -/
theorem projectiveSpaceTwistOneLocalFrames : ProjectiveSpaceTwistOneLocalFramesStatement.{u} := by
  intro R _ n
  have h : ∀ i : Fin (n + 1),
      Langlands.SchemeModule.TrivializesOn (twistOne R n)
        (twistOneCoordinate R n i) (projectiveSpaceCoordinateOpen R n i) := fun i =>
    ProjTwist.trivializesOn_projTwistingSheafSection (projectiveSpace_X_mem R n i) le_rfl
  exact ⟨h, isLocallyFreeRankOne_twistOne_of_coordinateFrames R n h⟩

end Langlands.AlgebraicGeometry
