import Langlands.Global.CuspidalTestExpansion.TranslateSpan
import Langlands.Global.AdelicIntertwiningHaarOffset
import Langlands.Global.AdelicIntertwiningClosedQuotient
import Langlands.Global.AdelicEisensteinCentralCovariance

/-! # Integrability of intertwining integrands along positive split translates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints PositiveRealTorus
  Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

variable {I₁ J : StandardIndex F G fam.i fam.ν} {n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
  {c : fam.M J ⟶ fam.M I₁} {K : Subgroup (AdelicGroupPoints F G)}
  [IsClosedImmersion (fam.p I₁).hom.hom.left]

omit [NumberField F] [IsClosedImmersion (fam.p I₁).hom.hom.left] in
/-- Right cancellation of a homomorphism of group schemes whose underlying morphism of
schemes is a monomorphism. -/
theorem _root_.Langlands.GroupScheme.cancel_mono_of_left
    {A B C : GroupScheme (Spec (CommRingCat.of F))}
    (f : B ⟶ C) [Mono f.hom.hom.left] {g h : A ⟶ B} (H : g ≫ f = h ≫ f) : g = h := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_mono f.hom.hom.left).mp (congrArg (fun z : A ⟶ C => z.hom.hom.left) H)

omit [NumberField F] [IsClosedImmersion (fam.p I₁).hom.hom.left] in
/-- An isomorphism of standard Levis restricts to an isomorphism of their specified split
components. -/
theorem exists_splitComponent_iso_of_iso (c : fam.M J ⟶ fam.M I₁) [IsIso c] :
    ∃ e : (fam.A J).toGrp ⟶ (fam.A I₁).toGrp, e ≫ fam.a I₁ = fam.a J ≫ c ∧ IsIso e := by
  have hJ : IsSplitComponent (fam.a J) := (fam.isCompatible J).splitComponent
  have hI : IsSplitComponent (fam.a I₁) := (fam.isCompatible I₁).splitComponent
  obtain ⟨e, he⟩ := hI.exists_factor hJ.1.1.1 (hJ.1.2.comp_iso (asIso c))
  obtain ⟨e', he'⟩ := hJ.exists_factor hI.1.1.1 (hI.1.2.comp_iso (asIso c).symm)
  refine ⟨e, he, ⟨e', ?_, ?_⟩⟩
  · have : Mono (fam.a J).hom.hom.left := hJ.1.1.mono
    apply cancel_mono_of_left (fam.a J)
    rw [Category.assoc, he', Category.id_comp]
    change e ≫ fam.a I₁ ≫ inv c = fam.a J
    rw [← Category.assoc, he]
    change (fam.a J ≫ c) ≫ inv c = fam.a J
    rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · have : Mono (fam.a I₁).hom.hom.left := hI.1.1.mono
    apply cancel_mono_of_left (fam.a I₁)
    rw [Category.assoc, he, Category.id_comp, ← Category.assoc, he']
    change (fam.a I₁ ≫ inv c) ≫ c = fam.a I₁
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- The integrand of a left translate by `b ∈ P_{I₁}(𝔸)` is a fixed multiple of the integrand of
`f` moved by `a = n b n⁻¹`. -/
theorem intertwiningIntegrand_unnormalizedAction_eq (hK : IsIwasawaCompact (fam.p I₁) K)
    (f : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F (fam.P I₁))
    {bP : AdelicGroupPoints F (fam.P I₁)} {aG : AdelicGroupPoints F G}
    (hconj : map F (fam.P I₁) G (fam.p I₁) bP =
      (innerAdelicPoint F G n)⁻¹ * aG * innerAdelicPoint F G n) (y : AdelicGroupPoints F G) :
    hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n
        (fam.unnormalizedAction I₁ bP f) lam y =
      fun q => parameterPower F (fam.P I₁) (-lam) bP * hK.parameterTwist f lam
        ((innerAdelicPoint F G n)⁻¹ * aG *
          ((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G
            (SubgroupFunctor.range (fam.iU J ≫ fam.p J))) : AdelicGroupPoints F G) * y) := by
  funext q
  set v := ((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G
    (SubgroupFunctor.range (fam.iU J ≫ fam.p J))) : AdelicGroupPoints F G)
  have hsplit : (innerAdelicPoint F G n)⁻¹ * aG * v * y =
      map F (fam.P I₁) G (fam.p I₁) bP * ((innerAdelicPoint F G n)⁻¹ * v * y) := by
    rw [hconj]
    group
  rw [hsplit]
  simp only [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist,
    hK.heightPower_map_mul, unnormalizedAction]
  have h1 : parameterPower F (fam.P I₁) (-lam) bP * parameterPower F (fam.P I₁) lam bP = 1 := by
    rw [← parameterPower_add, neg_add_cancel]
    simp [parameterPower]
  linear_combination (-(f (map F (fam.P I₁) G (fam.p I₁) bP * ((innerAdelicPoint F G n)⁻¹ * v * y)) *
    hK.heightPower lam ((innerAdelicPoint F G n)⁻¹ * v * y))) * h1

set_option maxHeartbeats 1600000 in
/-- If the intertwining integrand of `f` is integrable at every adelic argument, so is the
integrand of every positive split translate of `f`, and hence of every element of the span of
these translates. -/
theorem integrable_intertwiningIntegrand_of_mem_translateSpan
    (hW : IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J) n c)
    (hK : IsIwasawaCompact (fam.p I₁) K) {f : AdelicGroupPoints F G → ℂ} (hfc : Continuous f)
    (hfU : IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁)) f)
    (lam : ComplexCharacterParameter F (fam.P I₁))
    (hf : ∀ y, Integrable (hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n f lam y)
      (intertwiningMeasure F (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J)
        (innerAdelicPoint F G n)))
    {h : AdelicGroupPoints F G → ℂ} (hh : h ∈ fam.translateSpan I₁ f) (y : AdelicGroupPoints F G) :
    Integrable (hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n h lam y)
      (intertwiningMeasure F (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J)
        (innerAdelicPoint F G n)) := by
  classical
  have hVr := (fam.isUnipotentRadical J).1
  have hUr := (fam.isUnipotentRadical I₁).1
  have : IsAffineHom (fam.U J).X.hom := IsClosedSubgroup.isAffineHom hVr.isClosedSubgroup
  have : Smooth (fam.U J).X.hom := hVr.smooth
  have : LocallyOfFiniteType (fam.U J).X.hom := inferInstance
  have hi : IsClosedSubgroup (fam.iU I₁ ≫ fam.p I₁) := fam.closedU I₁
  have : IsIso c := hW.isIso
  induction hh using Submodule.span_induction generalizing y with
  | mem x hx =>
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hb
    let m : AdelicGroupPoints F (fam.M J) :=
      map F (fam.M I₁) (fam.M J) (inv c) (map F (fam.A I₁).toGrp (fam.M I₁) (fam.a I₁) t)
    have hm : map F (fam.M J) (fam.M I₁) c m = map F (fam.A I₁).toGrp (fam.M I₁) (fam.a I₁) t := by
      simp only [m, ← map_comp_apply_of_hom]
      simp [map_apply]
    let bP := pointMap F (fam.A I₁).toGrp (fam.P I₁) (Adeles F) (fam.a I₁ ≫ fam.l I₁) t
    have hbP : bP = map F (fam.M I₁) (fam.P I₁) (fam.l I₁) (map F (fam.M J) (fam.M I₁) c m) := by
      rw [hm, ← map_comp_apply_of_hom]
      rfl
    let aG := map F (fam.P J) G (fam.p J) (map F (fam.M J) (fam.P J) (fam.l J) m)
    have hconj : map F (fam.P I₁) G (fam.p I₁) bP =
        (innerAdelicPoint F G n)⁻¹ * aG * innerAdelicPoint F G n := by
      rw [hbP]
      exact hW.adelic_comp_eq m
    let α := EisensteinConstantTerm.conjAdelic (fam.p J) (fam.iU J) hVr.isNormal
      (map F (fam.M J) (fam.P J) (fam.l J) m)
    have hα := conjAdelic_mem_intertwiningAdelicStabilizer_iff (fam.iU I₁) (fam.iU J) hW
      hUr.isNormal hVr.isNormal m
    have hconjI := intertwiningIntegralConjugation (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J) n
      hi hVr.smooth hVr.connectedSpace hVr.isUnipotent aG α hα (fun v => rfl) K hK f hfc hfU
      hUr.isUnipotent lam y
    obtain ⟨-, hiff, -⟩ := hconjI
    have hmoved := hiff.mp (hf (aG * y))
    have heq := fam.intertwiningIntegrand_unnormalizedAction_eq (J := J) hK f lam hconj y
    change Integrable (hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n
      (fam.unnormalizedAction I₁ bP f) lam y) _
    rw [heq]
    exact hmoved.const_mul _
  | zero =>
    have : hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n 0 lam y = 0 := by
      funext q
      simp [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist]
    rw [this]
    exact integrable_zero _ _ _
  | add a b _ _ ha hb =>
    have : hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n (a + b) lam y =
        hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n a lam y +
          hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n b lam y := by
      funext q
      simp [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist, add_mul]
    rw [this]
    exact (ha y).add (hb y)
  | smul z a _ ha =>
    have : hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n (z • a) lam y =
        fun q => z * hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n a lam y q := by
      funext q
      simp [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist, mul_assoc]
    rw [this]
    exact (ha y).const_mul z

set_option maxHeartbeats 2400000 in
/-- The intertwining integral carries the span of the positive split translates of `f` along
`I₁` into the span of the positive split translates of its value along `J`. -/
theorem intertwiningIntegral_mem_translateSpan
    (hW : IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J) n c)
    (hK : IsIwasawaCompact (fam.p I₁) K) {f : AdelicGroupPoints F G → ℂ} (hfc : Continuous f)
    (hfU : IsLeftInvariantUnder F G (parabolicUnipotentImage F (fam.p I₁) (fam.iU I₁)) f)
    (lam : ComplexCharacterParameter F (fam.P I₁))
    (hf : ∀ y, Integrable (hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n f lam y)
      (intertwiningMeasure F (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J)
        (innerAdelicPoint F G n)))
    {h : AdelicGroupPoints F G → ℂ} (hh : h ∈ fam.translateSpan I₁ f) :
    hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n h lam ∈
      fam.translateSpan J (hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n f lam) := by
  classical
  have hVr := (fam.isUnipotentRadical J).1
  have hUr := (fam.isUnipotentRadical I₁).1
  have : IsAffineHom (fam.U J).X.hom := IsClosedSubgroup.isAffineHom hVr.isClosedSubgroup
  have : Smooth (fam.U J).X.hom := hVr.smooth
  have : LocallyOfFiniteType (fam.U J).X.hom := inferInstance
  have hi : IsClosedSubgroup (fam.iU I₁ ≫ fam.p I₁) := fam.closedU I₁
  have : IsIso c := hW.isIso
  obtain ⟨e, he, hei⟩ := fam.exists_splitComponent_iso_of_iso c
  let Int := fun h' : AdelicGroupPoints F G → ℂ =>
    hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n h' lam
  have hInt : ∀ {h' : AdelicGroupPoints F G → ℂ}, h' ∈ fam.translateSpan I₁ f → ∀ y,
      Integrable (hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n h' lam y)
        (intertwiningMeasure F (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J)
          (innerAdelicPoint F G n)) := fun hh' y =>
    fam.integrable_intertwiningIntegrand_of_mem_translateSpan hW hK hfc hfU lam hf hh' y
  induction hh using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨b, hb⟩, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hb
    let t' : intrinsicSubgroup F (fam.A J) :=
      ⟨pointMap F (fam.A I₁).toGrp (fam.A J).toGrp (Adeles F) (inv e) t,
        map_intrinsicSubgroup_le F (fam.A I₁) (fam.A J) (Additive.ofMul (inv e)) ⟨t, ht, rfl⟩⟩
    let m : AdelicGroupPoints F (fam.M J) := map F (fam.A J).toGrp (fam.M J) (fam.a J) t'.val
    have hm : map F (fam.M J) (fam.M I₁) c m = map F (fam.A I₁).toGrp (fam.M I₁) (fam.a I₁) t := by
      have hc' : inv e ≫ fam.a J ≫ c = fam.a I₁ := by
        rw [← he, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      simp only [m, t', ← map_comp_apply_of_hom]
      rw [show pointMap F (fam.A I₁).toGrp (fam.A J).toGrp (Adeles F) (inv e) t =
        map F (fam.A I₁).toGrp (fam.A J).toGrp (inv e) t from rfl, ← map_comp_apply_of_hom]
      simp only [hc']
    let bP := pointMap F (fam.A I₁).toGrp (fam.P I₁) (Adeles F) (fam.a I₁ ≫ fam.l I₁) t
    have hbP : bP = map F (fam.M I₁) (fam.P I₁) (fam.l I₁) (map F (fam.M J) (fam.M I₁) c m) := by
      rw [hm, ← map_comp_apply_of_hom]
      rfl
    let xQ := positivePointMap F (fam.P J) (fam.A J) (fam.a J ≫ fam.l J) t'
    have hxQ : xQ = map F (fam.M J) (fam.P J) (fam.l J) m := by
      simp only [xQ, positivePointMap_apply, m, ← map_comp_apply_of_hom]
    let aG := map F (fam.P J) G (fam.p J) xQ
    have hconj : map F (fam.P I₁) G (fam.p I₁) bP =
        (innerAdelicPoint F G n)⁻¹ * aG * innerAdelicPoint F G n := by
      rw [hbP]
      change _ = _ * map F (fam.P J) G (fam.p J) xQ * _
      rw [hxQ]
      exact hW.adelic_comp_eq m
    let α := positiveIntertwiningRadicalAction (q := fam.p J) (l' := fam.l J) (a := fam.a J)
      (fam.iU J) hVr.isNormal t'
    have hα := positiveIntertwiningRadicalAction_mem_stabilizer (a := fam.a J) (fam.iU I₁)
      (fam.iU J) hW hUr.isNormal hVr.isNormal t'
    have hxQmem : xQ ∈ fam.positiveSplitComponent J := ⟨t'.val, t'.property, rfl⟩
    have hconjI := intertwiningIntegralConjugation (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J) n
      hi hVr.smooth hVr.connectedSpace hVr.isUnipotent aG α hα (fun v => rfl) K hK f hfc hfU
      hUr.isUnipotent lam
    obtain ⟨R, hR0, hR⟩ : ∃ R : ℂ, R ≠ 0 ∧ ∀ y,
        hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n f lam (aG * y) =
          R * ∫ q, hK.parameterTwist f lam ((innerAdelicPoint F G n)⁻¹ * aG *
            ((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G
              (SubgroupFunctor.range (fam.iU J ≫ fam.p J))) : AdelicGroupPoints F G) * y)
            ∂intertwiningMeasure F (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J)
              (innerAdelicPoint F G n) := by
      have hVcl := AdelicSubgroupPoints.isClosed_adelicPoints_range F G (fam.iU J ≫ fam.p J)
      have : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G
          (SubgroupFunctor.range (fam.iU J ≫ fam.p J))) := hVcl.locallyCompactSpace
      have hHcl := (intertwiningStabilizer (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J) n
        (inferInstance : IsClosedImmersion (fam.iU J ≫ fam.p J).hom.hom.left) hi
        hVr.isUnipotent).1
      have : LocallyCompactSpace (intertwiningAdelicStabilizer (fam.p I₁) (fam.iU I₁)
          (fam.iU J ≫ fam.p J) n) := hHcl.locallyCompactSpace
      refine ⟨_, ?_, fun y => (hconjI y).1⟩
      norm_cast
      exact (div_pos (mulEquivHaarChar_pos _) (mulEquivHaarChar_pos _)).ne'
    have hkey : Int (fam.unnormalizedAction I₁ bP f) =
        (parameterPower F (fam.P I₁) (-lam) bP * R⁻¹) •
          fam.splitComponentRepresentation J ⟨xQ, hxQmem⟩ (Int f) := by
      funext y
      have heq := fam.intertwiningIntegrand_unnormalizedAction_eq (J := J) hK f lam hconj y
      change ∫ q, hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n
          (fam.unnormalizedAction I₁ bP f) lam y q
            ∂intertwiningMeasure F (fam.p I₁) (fam.iU I₁) (fam.iU J ≫ fam.p J)
              (innerAdelicPoint F G n) =
        (parameterPower F (fam.P I₁) (-lam) bP * R⁻¹) * Int f (aG * y)
      rw [heq, integral_const_mul]
      change _ = _ * hK.intertwiningIntegral (fam.iU I₁) (fam.iU J ≫ fam.p J) n f lam (aG * y)
      rw [hR]
      field_simp
    change Int (fam.unnormalizedAction I₁ bP f) ∈ _
    rw [hkey]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨xQ, hxQmem⟩, rfl⟩)
  | zero =>
    have : Int 0 = 0 := by
      funext y
      simp [Int, IsIwasawaCompact.intertwiningIntegral, IsIwasawaCompact.intertwiningIntegrand,
        IsIwasawaCompact.parameterTwist]
    change Int 0 ∈ _
    rw [this]
    exact Submodule.zero_mem _
  | add a b ha hb iha ihb =>
    have : Int (a + b) = Int a + Int b := by
      funext y
      have hsum : hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n (a + b) lam y =
          hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n a lam y +
            hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n b lam y := by
        funext q
        simp [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist, add_mul]
      simp only [Int, IsIwasawaCompact.intertwiningIntegral, Pi.add_apply, hsum]
      exact integral_add (hInt ha y) (hInt hb y)
    change Int (a + b) ∈ _
    rw [this]
    exact Submodule.add_mem _ iha ihb
  | smul z a ha iha =>
    have : Int (z • a) = z • Int a := by
      funext y
      have hsm : hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n (z • a) lam y =
          fun q => z * hK.intertwiningIntegrand (fam.iU I₁) (fam.iU J ≫ fam.p J) n a lam y q := by
        funext q
        simp [IsIwasawaCompact.intertwiningIntegrand, IsIwasawaCompact.parameterTwist, mul_assoc]
      simp only [Int, IsIwasawaCompact.intertwiningIntegral, Pi.smul_apply, smul_eq_mul, hsm]
      exact integral_const_mul z _
    change Int (z • a) ∈ _
    rw [this]
    exact Submodule.smul_mem _ z iha

end Langlands.Global.StandardParabolicFamily
