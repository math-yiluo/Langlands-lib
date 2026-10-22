import Langlands.Cohomology.Tate.ShiftDefinitions
import Mathlib.CategoryTheory.Abelian.ShortExact

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]

/-- Extend a scalar-linear map to an equivariant map into the actual coinduced replacement. -/
def coinducedExtend {E A : Rep.{u} R G} (r : E →ₗ[R] A) : E ⟶ coinduced A :=
  Rep.ofHom ⟨(coinducedFunctions A).toLinearMap.comp
    (LinearMap.pi (fun g : G => r.comp (E.ρ g))), fun h => by
      apply LinearMap.ext
      intro e
      apply Subtype.ext
      funext g
      change r (E.ρ g (E.ρ h e)) = r (E.ρ (g * h) e)
      rw [map_mul, Module.End.mul_apply]⟩

lemma coinducedExtend_apply {E A : Rep.{u} R G} (r : E →ₗ[R] A) (e : E) (g : G) :
    ((coinducedExtend r).hom e).1 g = r (E.ρ g e) := rfl

lemma scalarSplit_shortExact (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) :
    S.ShortExact :=
  CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))
    { exact := s.exact, mono_f := s.mono_f, epi_g := s.epi_g }

lemma coinducedExtend_retraction (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) :
    S.f ≫ coinducedExtend s.r.hom = coinducedEmbedding S.X₁ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  funext g
  change s.r.hom (S.X₂.ρ g (S.f.hom a)) = S.X₁.ρ g a
  rw [← Rep.hom_comm_apply S.f g a]
  exact ConcreteCategory.congr_hom s.f_r (S.X₁.ρ g a)

/-- Compare a scalar-split coefficient sequence to the canonical embedding sequence. -/
def splitSequenceToShiftUp (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) :
    S ⟶ shiftUpSequence S.X₁ := by
  have hS := scalarSplit_shortExact S s
  have := hS.epi_g
  let e := coinducedExtend s.r.hom
  have he : S.f ≫ (e ≫ cokernel.π (coinducedEmbedding S.X₁)) = 0 := by
    rw [← Category.assoc, coinducedExtend_retraction S s, cokernel.condition]
  exact
    { τ₁ := 𝟙 _
      τ₂ := e
      τ₃ := hS.exact.desc (e ≫ cokernel.π (coinducedEmbedding S.X₁)) he
      comm₁₂ := by simpa using (coinducedExtend_retraction S s).symm
      comm₂₃ := (hS.exact.g_desc _ he).symm }

variable [Fintype G]

/-- Extend a scalar-linear section from the actual coinduced replacement by a finite sum. -/
def coinducedDescLinear {A E : Rep.{u} R G} (s : A →ₗ[R] E) : coinduced A →ₗ[R] E :=
  ∑ g : G, (E.ρ g⁻¹).comp
    (s.comp ((LinearMap.proj g).comp (coinducedFunctions A).symm.toLinearMap))

lemma coinducedDescLinear_apply {A E : Rep.{u} R G} (s : A →ₗ[R] E) (f : coinduced A) :
    coinducedDescLinear s f = ∑ g : G, E.ρ g⁻¹ (s (f.1 g)) := by
  simp [coinducedDescLinear, coinducedFunctions]

lemma coinducedDescLinear_equivariant {A E : Rep.{u} R G} (s : A →ₗ[R] E)
    (h : G) (f : coinduced A) :
    coinducedDescLinear s ((coinduced A).ρ h f) = E.ρ h (coinducedDescLinear s f) := by
  rw [coinducedDescLinear_apply, coinducedDescLinear_apply]
  change (∑ g : G, E.ρ g⁻¹ (s (f.1 (g * h)))) = E.ρ h (∑ g : G, E.ρ g⁻¹ (s (f.1 g)))
  calc
    _ = ∑ g : G, E.ρ h (E.ρ (g * h)⁻¹ (s (f.1 (g * h)))) := by
      apply Finset.sum_congr rfl
      intro g _
      simp [← Module.End.mul_apply, ← map_mul, mul_inv_rev]
    _ = ∑ g : G, E.ρ h (E.ρ g⁻¹ (s (f.1 g))) :=
      Equiv.sum_comp (Equiv.mulRight h) (fun g => E.ρ h (E.ρ g⁻¹ (s (f.1 g))))
    _ = _ := (map_sum _ _ _).symm

/-- The finite-sum extension is an actual representation morphism. -/
def coinducedDesc {A E : Rep.{u} R G} (s : A →ₗ[R] E) : coinduced A ⟶ E :=
  Rep.ofHom ⟨coinducedDescLinear s, fun h => by
    ext f
    exact coinducedDescLinear_equivariant s h f⟩

lemma coinducedDesc_section (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) :
    coinducedDesc s.s.hom ≫ S.g = coinducedProjection S.X₃ := by
  ext f
  change S.g.hom (coinducedDescLinear s.s.hom f) = coinducedProjectionLinear S.X₃ f
  rw [coinducedDescLinear_apply, coinducedProjectionLinear_apply, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Rep.hom_comm_apply]
  exact congrArg (S.X₃.ρ g⁻¹) (ConcreteCategory.congr_hom s.s_g (f.1 g))

/-- Compare the canonical augmentation sequence to a scalar-split coefficient sequence. -/
def shiftDownToSplitSequence (S : ShortComplex (Rep.{u} R G))
    (s : (S.map (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).Splitting) :
    shiftDownSequence S.X₃ ⟶ S := by
  have hS := scalarSplit_shortExact S s
  have := hS.mono_f
  let e := coinducedDesc s.s.hom
  have he : (kernel.ι (coinducedProjection S.X₃) ≫ e) ≫ S.g = 0 := by
    rw [Category.assoc, coinducedDesc_section S s, kernel.condition]
  exact
    { τ₁ := hS.exact.lift (kernel.ι (coinducedProjection S.X₃) ≫ e) he
      τ₂ := e
      τ₃ := 𝟙 _
      comm₁₂ := hS.exact.lift_f _ he
      comm₂₃ := by simpa using coinducedDesc_section S s }

end Langlands.Tate
