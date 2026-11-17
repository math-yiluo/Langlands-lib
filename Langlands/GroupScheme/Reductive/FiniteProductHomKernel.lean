import Langlands.GroupScheme.CommutingFamilyMultiplication
import Langlands.GroupScheme.Reductive.FiniteProductCenter
import Langlands.GroupScheme.Reductive.SemisimpleFiniteProduct
import Langlands.GroupScheme.Reductive.CommutingMultiplicationIsogeny
import Langlands.GroupScheme.Reductive.AdjointRootSpan
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Kernels of homomorphisms that embed each finite-product factor -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Base
variable {S : Scheme.{u}} {I : Type u} [Finite I] (H : I → GroupScheme S)
    {G : GroupScheme S}

/-- Conjugation of a single-coordinate point stays in that coordinate. -/
theorem pi_conjugate_factor (i : I) {T : Over S} (x : T ⟶ (pi H).X)
    (y : T ⟶ (H i).X) :
    x * (y ≫ (piFactorInclusionHom H i).hom.hom) * x⁻¹ =
      ((piPointsEquiv H T x i) * y * (piPointsEquiv H T x i)⁻¹) ≫
        (piFactorInclusionHom H i).hom.hom := by
  apply (piPointsEquiv H T).injective
  funext z
  simp only [piPointsEquiv_apply, MonObj.mul_comp, GrpObj.inv_comp]
  by_cases hz : i = z
  · subst z
    rw [piFactorInclusionHom_points_self, piFactorInclusionHom_points_self]
  · rw [piFactorInclusionHom_points_ne H i z hz,
      piFactorInclusionHom_points_ne H i z hz]
    simp only [mul_one, mul_inv_cancel]

/-- A homomorphism from a finite product which is monic on each factor has
central full kernel. -/
theorem piHom_mem_center_of_comp_eq_one (f : pi H ⟶ G)
    (hmono : ∀ i, Mono (piFactorInclusionHom H i ≫ f).hom.hom)
    {T : Over S} (x : T ⟶ (pi H).X) (hx : x ≫ f.hom.hom = 1) :
    x ∈ (center (pi H)).carrier T := by
  apply (mem_center_pi_iff H x).mpr
  intro i T' a y
  let : Mono (piFactorInclusionHom H i ≫ f).hom.hom := hmono i
  have hres : (a ≫ x) ≫ f.hom.hom = 1 := by
    rw [Category.assoc, hx, MonObj.comp_one]
  have he : (piPointsEquiv H T' (a ≫ x) i) * y *
      (piPointsEquiv H T' (a ≫ x) i)⁻¹ = y := by
    apply (cancel_mono (piFactorInclusionHom H i ≫ f).hom.hom).mp
    change ((_ * y * _) ≫ (piFactorInclusionHom H i).hom.hom) ≫ f.hom.hom =
      (y ≫ (piFactorInclusionHom H i).hom.hom) ≫ f.hom.hom
    rw [← pi_conjugate_factor H i (a ≫ x) y]
    simp only [MonObj.mul_comp, GrpObj.inv_comp, hres, one_mul, inv_one, mul_one]
  apply (commute_iff_eq _ _).mpr
  have ha := congrFun (piPointsEquiv_naturality H a x) i
  rw [ha] at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- Factorwise monomorphisms suffice to centralize the actual scheme kernel. -/
theorem isCentral_kernelι_piHom (f : pi H ⟶ G)
    (hmono : ∀ i, Mono (piFactorInclusionHom H i ≫ f).hom.hom) :
    IsCentral (kernelι f) := by
  apply (isCentral_kernelι_iff f).mpr
  exact fun _ x hx => piHom_mem_center_of_comp_eq_one H f hmono x hx

/-- A flat surjective group-scheme map sends the full centre into the full centre. -/
theorem mem_center_comp_of_flat_surjective {D C : GroupScheme S} (f : D ⟶ C)
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left]
    {T : Over S} {x : T ⟶ D.X} (hx : x ∈ (center D).carrier T) :
    x ≫ f.hom.hom ∈ (center C).carrier T := by
  intro T' a y
  let V : Over S := Over.mk (pullback.fst y.left f.hom.hom.left ≫ T'.hom)
  let b : V ⟶ T' := Over.homMk (pullback.fst y.left f.hom.hom.left) rfl
  let z : V ⟶ D.X := Over.homMk (pullback.snd y.left f.hom.hom.left) (by
    rw [← Over.w f.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w y]
    rfl)
  have hb : Epi b.left := by
    change Epi (pullback.fst y.left f.hom.hom.left)
    exact Flat.epi_of_flat_of_surjective _
  let : Epi b := Over.epi_of_epi_left _
  have hz : b ≫ y = z ≫ f.hom.hom := Over.OverMorphism.ext pullback.condition
  apply (commute_iff_eq _ _).mpr
  apply (cancel_epi b).mp
  simp only [MonObj.comp_mul, hz]
  have he := congrArg (fun q => q ≫ f.hom.hom) (hx V (b ≫ a) z).eq
  simpa only [MonObj.mul_comp, Category.assoc] using he

/-- A point supported in one coordinate is central when that coordinate is central. -/
theorem mem_center_piFactorInclusionHom (i : I) {T : Over S} {x : T ⟶ (H i).X}
    (hx : x ∈ (center (H i)).carrier T) :
    x ≫ (piFactorInclusionHom H i).hom.hom ∈ (center (pi H)).carrier T := by
  apply (mem_center_pi_iff H _).mpr
  intro z
  by_cases hz : i = z
  · subst z
    simpa only [piPointsEquiv_apply, piFactorInclusionHom_points_self] using hx
  · simp only [piPointsEquiv_apply, piFactorInclusionHom_points_ne H i z hz]
    exact (center (H z)).carrier T |>.one_mem

/-- A factorwise monic flat surjection onto a centre-free group has a
centre-free source product. -/
theorem center_pi_eq_bot_of_flat_surjective_piHom (f : pi H ⟶ G)
    [Flat f.hom.hom.left] [Surjective f.hom.hom.left]
    (hmono : ∀ i, Mono (piFactorInclusionHom H i ≫ f).hom.hom)
    (hc : center G = ⊥) : center (pi H) = ⊥ := by
  apply (center_pi_eq_bot_iff H).mpr
  intro i
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  constructor
  · intro hx
    let : Mono (piFactorInclusionHom H i ≫ f).hom.hom := hmono i
    have hz := mem_center_comp_of_flat_surjective f (mem_center_piFactorInclusionHom H i hx)
    rw [hc, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hz
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
    apply (cancel_mono (piFactorInclusionHom H i ≫ f).hom.hom).mp
    simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.one_comp] using hz
  · rintro hx
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    rw [hx]
    exact (center (H i)).carrier T |>.one_mem

end Base

section Field
variable {k : Type u} [Field k] {I : Type u} [Finite I]
    (H : I → GroupScheme (Spec (CommRingCat.of k)))
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A surjection from a finite product of semisimple groups to a smooth affine
group, monic on each factor, is an actual central isogeny. -/
theorem isCentralIsogeny_piHom_of_surjective (f : pi H ⟶ G)
    (hH : ∀ i, IsSemisimple (H i)) (hG : IsConnectedReductive G)
    (hmono : ∀ i, Mono (piFactorInclusionHom H i ≫ f).hom.hom)
    (hs : Surjective f.hom.hom.left) : IsCentralIsogeny f := by
  have hP := IsSemisimple.pi H hH
  let : IsAffineHom (pi H).X.hom := hP.isConnectedReductive.isAffineHom
  let : Smooth (pi H).X.hom := hP.isConnectedReductive.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Surjective f.hom.hom.left := hs
  let : Flat f.hom.hom.left := flat_of_surjective f
  let : QuasiCompact f.hom.hom.left := inferInstance
  have hcen := isCentral_kernelι_piHom H f hmono
  let : IsFinite (kernel f).X.hom :=
    isFinite_of_isClosedSubgroup_of_isCentral_of_hasFiniteCenter
      (kernelι f) (inferInstanceAs (IsClosedImmersion (kernelι f).hom.hom.left))
      hcen hP.hasFiniteCenter
  let : IsFinite f.hom.hom.left := isFinite_of_finite_kernel f
  let : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, hcen⟩

/-- Such a surjection onto a simply connected group is an isomorphism. -/
theorem isIso_piHom_of_isSimplyConnected (f : pi H ⟶ G)
    (hH : ∀ i, IsSemisimple (H i)) (hG : IsSimplyConnected G)
    (hmono : ∀ i, Mono (piFactorInclusionHom H i ≫ f).hom.hom)
    (hs : Surjective f.hom.hom.left) : IsIso f :=
  hG.central_isogeny_isIso (pi H) f (IsSemisimple.pi H hH)
    (isCentralIsogeny_piHom_of_surjective H f hH hG.isSemisimple.isConnectedReductive hmono hs)

/-- Such a surjection onto an adjoint group is an isomorphism. -/
theorem isIso_piHom_of_isAdjoint (f : pi H ⟶ G)
    (hH : ∀ i, IsSemisimple (H i)) (hG : IsAdjoint G)
    (hmono : ∀ i, Mono (piFactorInclusionHom H i ≫ f).hom.hom)
    (hs : Surjective f.hom.hom.left) : IsIso f := by
  have hf := isCentralIsogeny_piHom_of_surjective H f hH
    hG.isSemisimple.isConnectedReductive hmono hs
  let : Flat f.hom.hom.left := hf.flat
  let : Surjective f.hom.hom.left := hf.surjective
  exact hf.isIso_of_center_eq_bot
    (center_pi_eq_bot_of_flat_surjective_piHom H f hmono hG.center_eq_bot)

end Field
end Langlands.GroupScheme
