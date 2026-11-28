import Langlands.AbelianScheme.AbelianInertiaSplitReduction
import Langlands.AbelianScheme.SplitTorsionModel
import Langlands.AbelianScheme.Tate.PrimeLevelMonodromyPGroup
import Langlands.AbelianScheme.Tate.FiniteTransport
import Langlands.AlgebraicGeometry.FiniteEtale.ArithmeticCyclotomicPower
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricPathProof
import Langlands.AlgebraicGeometry.FiniteEtale.PathPushforward
import Langlands.AlgebraicGeometry.FiniteEtale.TameConjugationStatement
import Langlands.AlgebraicGeometry.FiniteEtale.WeaklyUnramifiedDvrQuotientLift
import Langlands.CommutativeAlgebra.ArithmeticRegularLocalApproximationStatement

/-! # The arithmetic chart argument for split prime torsion -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.AlgebraicGeometry.PointTopology
open Langlands.CommutativeAlgebra
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.AbelianScheme

private def identityCoverLift {S : Scheme.{u}} {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ S) : Fiber s (cover (𝟙 S)) := Over.homMk s (by simp [cover])

private theorem identityCoverLift_eq_left {S : Scheme.{u}} {Ω : Type u} [Field Ω]
    (s : Spec (.of Ω) ⟶ S) (x : Fiber s (cover (𝟙 S))) : x.left = s := by
  have hx := Over.w x
  change x.left ≫ 𝟙 _ = s at hx
  simpa using hx

private theorem sections_exhaust_fibre {S Z : Scheme.{u}}
    (f : Z ⟶ S) (Y : Cover S) {Ω Ω' : Type u} [Field Ω] [Field Ω']
    (s : Spec (.of Ω) ⟶ Z) (t : Spec (.of Ω') ⟶ Z)
    (hs : ∀ X : Cover Z, Finite (Fiber s X)) (ht : ∀ X : Cover Z, Finite (Fiber t X))
    (hsf : ∀ X : Cover S, Finite (Fiber (s ≫ f) X)) (htf : ∀ X : Cover S, Finite (Fiber (t ≫ f) X))
    (p : fiberFunctor s hs ≅ fiberFunctor t ht)
    (hx : ∀ x : Fiber (s ≫ f) Y, ∃ σ : Over.mk f ⟶ Y.obj, s ≫ σ.left = x.left)
    (x : Fiber (t ≫ f) Y) : ∃ σ : Over.mk f ⟶ Y.obj, t ≫ σ.left = x.left := by
  let pathEquiv : Fiber (s ≫ f) Y ≃ Fiber (t ≫ f) Y :=
    FintypeCat.equivEquivIso.symm ((pathPushforward f hsf htf p).app Y)
  obtain ⟨x₀, rfl⟩ := pathEquiv.surjective x
  obtain ⟨σ, hσ⟩ := hx x₀
  have hφ : σ.left ≫ Y.obj.hom = (cover (𝟙 Z)).obj.hom ≫ f :=
    (Over.w σ).trans (Category.id_comp f).symm
  have hh := pathPushforward_apply_left_of_comp f hsf htf p x₀ (identityCoverLift s) σ.left hφ hσ
  have hpoint : (p.hom.app (cover (𝟙 Z)) (identityCoverLift s)).left = t :=
    identityCoverLift_eq_left t _
  exact ⟨σ, (congrArg (· ≫ σ.left) hpoint).symm.trans hh.symm⟩

private theorem fibre_action_trivial_of_sections {S Z : Scheme.{u}} (f : Z ⟶ S) (Y : Cover S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Z)
    (hx : ∀ x : Fiber (s ≫ f) Y, ∃ σ : Over.mk f ⟶ Y.obj, s ≫ σ.left = x.left)
    (g : FundamentalGroup s (geometricFiberFinite s)) (x : Fiber (s ≫ f) Y) :
    fundamentalGroupMap f s (s ≫ f) rfl (geometricFiberFinite s) (geometricFiberFinite (s ≫ f)) g • x = x := by
  obtain ⟨σ, hσ⟩ := hx x
  apply Over.OverMorphism.ext
  have hφ : σ.left ≫ Y.obj.hom = (cover (𝟙 Z)).obj.hom ≫ f :=
    (Over.w σ).trans (Category.id_comp f).symm
  rw [fundamentalGroupMap_smul_left_of_comp f s (s ≫ f) rfl (geometricFiberFinite s)
    (geometricFiberFinite (s ≫ f)) g x (identityCoverLift s) σ.left hφ hσ,
    identityCoverLift_eq_left, hσ]

private theorem model_prime_action_trivial
    {L Ω Ω' : Type u} [Field L] [Field Ω] [Field Ω'] [IsAlgClosed Ω] [IsAlgClosed Ω']
    (C D : Subalgebra ℤ L) (hCD : C ≤ D) (hD : D.FG)
    (s : Spec (.of Ω) ⟶ Spec (.of L)) (A₀ : AbelianScheme (Spec (.of ↥C)))
    (n : ℕ) (hn : 0 < n) (hu₀ : IsUnit (n : Γ(Spec (.of ↥C), ⊤)))
    (hpts : letI : Algebra ↥C ↥D := (Subalgebra.inclusion hCD).toRingHom.toAlgebra
      ∀ x : Fiber (s ≫ Spec.algebraMap ↥C L) (Tate.torsionCover torsionFiniteEtale A₀ n hn hu₀),
        ∃ v : RingPoint ↥C (Tate.torsionCover torsionFiniteEtale A₀ n hn hu₀).obj ↥D,
          s ≫ Spec.algebraMap ↥D L ≫ v.left = x.left)
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of ↥D)) (t : Spec (.of Ω') ⟶ Z) :
    let b := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCD).toRingHom)
    let a := f ≫ b
    let hu := Tate.isUnit_natCast_pullback a n hu₀
    ∀ (g : FundamentalGroup t (geometricFiberFinite t)) (x : Tate.Level ((baseChange a).obj A₀) (Over.mk t) n),
      Tate.levelMonodromy t (geometricFiberFinite t) torsionFiniteEtale ((baseChange a).obj A₀) n hn hu g x = x := by
  dsimp only
  intro g x
  let : Algebra ↥C ↥D := (Subalgebra.inclusion hCD).toRingHom.toAlgebra
  let b := Spec.algebraMap ↥C ↥D
  let a := f ≫ b
  let sD := s ≫ Spec.algebraMap ↥D L
  let Y := Tate.torsionCover torsionFiniteEtale A₀ n hn hu₀
  have hs : sD ≫ b = s ≫ Spec.algebraMap ↥C L := by
    rw [show sD = s ≫ Spec.algebraMap ↥D L from rfl, Category.assoc]
    congr 1
    change Spec.map (CommRingCat.ofHom (algebraMap ↥D L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ↥C ↥D)) =
        Spec.map (CommRingCat.ofHom (algebraMap ↥C L))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hptsD (y : Fiber (sD ≫ b) Y) : ∃ v : Over.mk b ⟶ Y.obj, sD ≫ v.left = y.left := by
    let y' : Fiber (s ≫ Spec.algebraMap ↥C L) Y := Over.homMk y.left ((Over.w y).trans hs)
    obtain ⟨v, hv⟩ := hpts y'
    exact ⟨v, (Category.assoc _ _ _).trans hv⟩
  have : Algebra.FiniteType ℤ ↥D := (Subalgebra.fg_iff_finiteType _).mp hD
  have : IsNoetherianRing ↥D := Algebra.FiniteType.isNoetherianRing ℤ ↥D
  have ht : (t ≫ f) ≫ b = t ≫ a := Category.assoc _ _ _
  have hptst (y : Fiber (t ≫ a) Y) : ∃ v : Over.mk a ⟶ Y.obj, t ≫ v.left = y.left := by
    let y' : Fiber ((t ≫ f) ≫ b) Y := Over.homMk y.left ((Over.w y).trans ht.symm)
    obtain ⟨v, hv⟩ := sections_exhaust_fibre b Y sD (t ≫ f) (geometricFiberFinite sD)
      (geometricFiberFinite (t ≫ f)) (geometricFiberFinite (sD ≫ b))
      (geometricFiberFinite ((t ≫ f) ≫ b))
      (geometricPathExists sD (t ≫ f) (geometricFiberFinite sD) (geometricFiberFinite (t ≫ f))).some
      hptsD y'
    have hw : (f ≫ v.left) ≫ Y.obj.hom = a := by rw [Category.assoc, Over.w v]; rfl
    exact ⟨Over.homMk (f ≫ v.left) hw, (Category.assoc _ _ _).symm.trans hv⟩
  let hu := Tate.isUnit_natCast_pullback a n hu₀
  obtain ⟨e, he⟩ := Tate.exists_levelBaseChange_intertwiner a t (t ≫ a) rfl A₀ n hn hu₀ hu
  refine e.injective ((he g x).trans ?_)
  obtain ⟨y, hy⟩ := (Tate.kernelLevelEquiv A₀ (Over.mk (t ≫ a)) n).surjective (e x)
  rw [← hy, Tate.levelMonodromy_kernel]
  exact congrArg (fun z : Fiber (t ≫ a) Y ↦ Tate.kernelLevelEquiv A₀ (Over.mk (t ≫ a)) n (Additive.ofMul z))
    (fibre_action_trivial_of_sections a Y t hptst g y.toMul)

private theorem exists_levelPath_intertwiner {S : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [Field Ω']
    [IsAlgClosed Ω] [IsAlgClosed Ω'] (s : Spec (.of Ω) ⟶ S) (t : Spec (.of Ω') ⟶ S)
    (p : fiberFunctor s (geometricFiberFinite s) ≅ fiberFunctor t (geometricFiberFinite t))
    (A : AbelianScheme S) (n : ℕ) (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤))) :
    ∃ e : Tate.Level A (Over.mk s) n ≃ₗ[ZMod n] Tate.Level A (Over.mk t) n,
      ∀ (g : FundamentalGroup s (geometricFiberFinite s)) (x : Tate.Level A (Over.mk s) n),
        e (Tate.levelMonodromy s (geometricFiberFinite s) torsionFiniteEtale A n hn hu g x) =
          Tate.levelMonodromy t (geometricFiberFinite t) torsionFiniteEtale A n hn hu
            (pathConjugation p g) (e x) := by
  let e : Tate.Level A (Over.mk s) n ≃ₗ[ZMod n] Tate.Level A (Over.mk t) n :=
    { Tate.levelTransport torsionFiniteEtale A n hn hu p with
      map_smul' := Tate.levelTransport_zmod_smul torsionFiniteEtale A n hn hu p }
  exact ⟨e, Tate.levelTransport_monodromy torsionFiniteEtale A n hn hu p⟩

private theorem pointedMap_of_square {S U V T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (f : T ⟶ U) (j : T ⟶ V) (b : U ⟶ S) (c : V ⟶ S) (hf : f ≫ b = j ≫ c)
    (t : Spec (.of Ω) ⟶ T) (s : Spec (.of Ω) ⟶ S) (hu : (t ≫ f) ≫ b = s) (hv : (t ≫ j) ≫ c = s)
    (g : FundamentalGroup t (geometricFiberFinite t)) :
    fundamentalGroupMap b (t ≫ f) s hu (geometricFiberFinite (t ≫ f)) (geometricFiberFinite s)
        (fundamentalGroupMap f t (t ≫ f) rfl (geometricFiberFinite t) (geometricFiberFinite (t ≫ f)) g) =
      fundamentalGroupMap c (t ≫ j) s hv (geometricFiberFinite (t ≫ j)) (geometricFiberFinite s)
        (fundamentalGroupMap j t (t ≫ j) rfl (geometricFiberFinite t) (geometricFiberFinite (t ≫ j)) g) := by
  have hcomp (a : T ⟶ S) (ha : t ≫ a = s) (a' : T ⟶ S) (ha' : t ≫ a' = s) (hh : a = a') :
      fundamentalGroupMap a t s ha (geometricFiberFinite t) (geometricFiberFinite s) =
        fundamentalGroupMap a' t s ha' (geometricFiberFinite t) (geometricFiberFinite s) := by
    subst a'
    rfl
  have h1 : t ≫ f ≫ b = s := (Category.assoc _ _ _).symm.trans hu
  have h2 : t ≫ j ≫ c = s := (Category.assoc _ _ _).symm.trans hv
  exact (DFunLike.congr_fun (fundamentalGroupMap_comp b (t ≫ f) s hu _ _ f t rfl h1 _) g).symm.trans
    ((DFunLike.congr_fun (hcomp _ h1 _ h2 hf) g).trans
      (DFunLike.congr_fun (fundamentalGroupMap_comp c (t ≫ j) s hv _ _ j t rfl h2 _) g))

private theorem exists_levelChart_intertwiner
    {S K U T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (i : T ⟶ K) (j : T ⟶ U) (b : K ⟶ S) (c : U ⟶ S) (hcomm : i ≫ b = j ≫ c)
    (t : Spec (.of Ω) ⟶ T) (A₀ : AbelianScheme S) (A : AbelianScheme K)
    (e : A ≅ (baseChange b).obj A₀) (n : ℕ) (hn : 0 < n)
    (hu₀ : IsUnit (n : Γ(S, ⊤))) (huK : IsUnit (n : Γ(K, ⊤))) (huU : IsUnit (n : Γ(U, ⊤))) :
    let sK := t ≫ i
    let sU := t ≫ j
    let iStar := fundamentalGroupMap i t sK rfl (geometricFiberFinite t) (geometricFiberFinite sK)
    let jStar := fundamentalGroupMap j t sU rfl (geometricFiberFinite t) (geometricFiberFinite sU)
    ∃ d : Tate.Level A (Over.mk sK) n ≃ₗ[ZMod n] Tate.Level ((baseChange c).obj A₀) (Over.mk sU) n,
      ∀ (g : FundamentalGroup t (geometricFiberFinite t)) (x : Tate.Level A (Over.mk sK) n),
        d (Tate.levelMonodromy sK (geometricFiberFinite sK) torsionFiniteEtale A n hn huK (iStar g) x) =
          Tate.levelMonodromy sU (geometricFiberFinite sU) torsionFiniteEtale
            ((baseChange c).obj A₀) n hn huU (jStar g) (d x) := by
  let sK := t ≫ i
  let sU := t ≫ j
  let s₀ := sU ≫ c
  have hK : sK ≫ b = s₀ := by
    change (t ≫ i) ≫ b = (t ≫ j) ≫ c
    rw [Category.assoc, Category.assoc, hcomm]
  obtain ⟨eK, heK⟩ := Tate.exists_levelBaseChange_intertwiner b sK s₀ hK A₀ n hn hu₀ huK
  obtain ⟨eU, heU⟩ := Tate.exists_levelBaseChange_intertwiner c sU s₀ rfl A₀ n hn hu₀ huU
  let eA := PolarizedFiniteLevel.levelIsoLinear e (Over.mk sK) n
  let iStar := fundamentalGroupMap i t sK rfl (geometricFiberFinite t) (geometricFiberFinite sK)
  let jStar := fundamentalGroupMap j t sU rfl (geometricFiberFinite t) (geometricFiberFinite sU)
  refine ⟨(eA.trans eK).trans eU.symm, fun g x ↦ eU.injective ?_⟩
  have h := Tate.levelMonodromy_map sK (geometricFiberFinite sK) torsionFiniteEtale A n hn huK
    e.hom (iStar g) x
  change Tate.levelMonodromy sK (geometricFiberFinite sK) torsionFiniteEtale ((baseChange b).obj A₀)
    n hn huK (iStar g) (eA x) = eA (Tate.levelMonodromy sK (geometricFiberFinite sK)
      torsionFiniteEtale A n hn huK (iStar g) x) at h
  simp only [LinearEquiv.trans_apply]
  rw [← h, heK, heU, pointedMap_of_square i j b c hcomm t s₀ hK rfl]
  let g₀ := fundamentalGroupMap c sU s₀ rfl (geometricFiberFinite sU) (geometricFiberFinite s₀) (jStar g)
  let T₀ := Tate.levelMonodromy s₀ (geometricFiberFinite s₀) torsionFiniteEtale A₀ n hn hu₀ g₀
  exact (eU.apply_symm_apply (T₀ (eK (eA x)))).trans
    (congrArg T₀ (eU.apply_symm_apply (eK (eA x))).symm)

private theorem levelEnd_conj_of_intertwines {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N] (d : M ≃ₗ[R] N)
    (F : Module.End R M) (G : Module.End R N) (h : ∀ x, d (F x) = G (d x)) :
    d.conj F = G := by
  apply LinearMap.ext
  intro x
  rw [LinearEquiv.conj_apply_apply, h, LinearEquiv.apply_symm_apply]

private theorem levelEnd_conj_of_equiv_conj {R M : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] (d F G : M ≃ₗ[R] M) (h : d * F * d⁻¹ = G) :
    d.conj F.toLinearMap = G.toLinearMap := by
  subst G
  rfl

open Tate.PrimeAdic

/-- Arithmetic approximation, Kummer factorization and tame divisor conjugation imply finite
Tate power conjugacy when the action on the prime torsion is trivial. -/
def AbelianInertiaArithmeticReductionStatement : Prop :=
  ArithmeticRegularLocalApproximationStatement.{u, u, u} →
    StrictlyHenselianKummerFactorizationStatement.{u, u} →
    RegularDivisorTameConjugationStatement.{u, u} →
    SplitAbelianInertiaPowerConjugacyStatement.{u}

/-- Descend the abelian scheme and its split prime torsion to one arithmetic chart.
Use the finite prime-group images and the cyclotomic exponent of that chart at each level. -/
theorem abelianInertiaArithmeticReduction : AbelianInertiaArithmeticReductionStatement.{u} := by
  intro hApprox hKummer hTame W L _ _ _ _ _ _ _ _ A ℓ hprime hℓ Ω _ _ s hu hfix g
  let hn₁ := hprime.out.pos
  let hu₁ : IsUnit (ℓ : Γ(Spec (.of L), ⊤)) := by simpa using hu 1
  obtain ⟨C, D, hCD, _, hD, A₀, hu₀, ⟨e⟩, hpts⟩ := splitTorsionModel L Ω s A ℓ hn₁ hu₁ hfix
  have : Algebra.FiniteType ℤ ↥D := (Subalgebra.fg_iff_finiteType _).mp hD
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨W', _, _, _, _, _, i, _, hiπ, _, B, _, _, _, _, tB, jB, hlocB, htB, htB', hregB, hjB,
      ⟨kB, hkB, hki⟩, iFrac, jAway, fD, hiFrac, hjAway, hDmap⟩ :=
    hApprox W L π ↥D (algebraMap ↥D L) hπ
  let L' := FractionRing W'
  let : Algebra B W' := jB.toAlgebra
  have : IsLocalHom (algebraMap B W') := hlocB
  have hℓW' : IsUnit (ℓ : W') := by simpa using hℓ.map i
  have hℓB : IsUnit (ℓ : B) :=
    (isUnit_map_iff jB _).mp (by simpa only [map_natCast] using hℓW')
  have hjEq : jAway = traitGenericRingHom L' tB hjB.ne_zero := by
    apply IsLocalization.ringHom_ext (Submonoid.powers tB)
    rw [hjAway]
    have hunit : IsUnit (((algebraMap W' L').comp (algebraMap B W')) tB) :=
      isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective W' L')).mpr hjB.ne_zero)
    exact (IsLocalization.Away.lift_comp tB hunit).symm
  let j := traitGenericMorphism L' tB hjB.ne_zero
  let f := Spec.map (CommRingCat.ofHom iFrac)
  let X := Spec (.of (Localization.Away tB))
  let b := Spec.algebraMap ↥C L
  let rD := Spec.map (CommRingCat.ofHom fD)
  let bD := Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCD).toRingHom)
  let c := rD ≫ bD
  have hcomm : f ≫ b = j ≫ c := by
    have hcomp : (algebraMap ↥D L).comp (Subalgebra.inclusion hCD).toRingHom = algebraMap ↥C L := rfl
    change Spec.map (CommRingCat.ofHom iFrac) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥C L)) =
      Spec.map (CommRingCat.ofHom (traitGenericRingHom L' tB hjB.ne_zero)) ≫
      Spec.map (CommRingCat.ofHom fD) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hCD).toRingHom)
    rw [← hjEq, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← RingHom.comp_assoc, hDmap, RingHom.comp_assoc, hcomp]
  let Ω' := AlgebraicClosure L'
  let t := Spec.algebraMap L' Ω'
  let sL := t ≫ f
  let sX := t ≫ j
  let hFinL := geometricFiberFinite sL
  let hFinX := geometricFiberFinite sX
  let hFin := geometricFiberFinite s
  let hFinT := geometricFiberFinite t
  let p := (geometricPathExists s sL hFin hFinL).some
  let fStar := fundamentalGroupMap f t sL rfl hFinT hFinL
  let jStar := fundamentalGroupMap j t sX rfl hFinT hFinX
  let A_X := (baseChange c).obj A₀
  let hu₀m (m : ℕ) : IsUnit ((ℓ ^ m : ℕ) : Γ(Spec (.of ↥C), ⊤)) := by simpa using hu₀.pow m
  let huX (m : ℕ) : IsUnit ((ℓ ^ m : ℕ) : Γ(X, ⊤)) :=
    Tate.isUnit_natCast_pullback c (ℓ ^ m) (hu₀m m)
  let hx₁ := Tate.isUnit_natCast_pullback c ℓ hu₀
  have htrivL : Tate.levelMonodromyHom sL hFinL A hn₁ hu₁ = 1 := by
    apply MonoidHom.ext
    intro gL
    obtain ⟨g₀, rfl⟩ := (pathConjugation p).surjective gL
    apply LinearEquiv.ext
    intro z
    obtain ⟨w, hw⟩ := exists_levelPath_intertwiner s sL p A ℓ hn₁ hu₁
    obtain ⟨y, rfl⟩ := w.surjective z
    change Tate.levelMonodromy sL hFinL torsionFiniteEtale A ℓ hn₁ hu₁
      (pathConjugation p g₀) (w y) = w y
    rw [← hw, hfix]
  have htrivX : Tate.levelMonodromyHom sX hFinX A_X hn₁ hx₁ = 1 := by
    apply MonoidHom.ext
    intro gX
    apply LinearEquiv.ext
    intro x
    exact model_prime_action_trivial C D hCD hD s A₀ ℓ hn₁ hu₀ hpts rD sX gX x
  obtain ⟨q, hq⟩ := arithmeticCyclotomicPower (ResidueField B) kB hkB hki ℓ
  have hq' : CyclotomicPowerCondition (ResidueField B) ℓ q := hq
  refine ⟨q, hq.1, fun n ↦ ?_⟩
  let m := ℓ ^ n
  let hpos := pow_pos hn₁ n
  let ρL := Tate.levelMonodromyHom sL hFinL A hpos (hu n)
  let ρX := Tate.levelMonodromyHom sX hFinX A_X hpos (huX n)
  let : TopologicalSpace (Tate.Level A (Over.mk sL) m ≃ₗ[ZMod m] Tate.Level A (Over.mk sL) m) := ⊥
  let : DiscreteTopology (Tate.Level A (Over.mk sL) m ≃ₗ[ZMod m] Tate.Level A (Over.mk sL) m) := ⟨rfl⟩
  let : TopologicalSpace (Tate.Level A_X (Over.mk sX) m ≃ₗ[ZMod m] Tate.Level A_X (Over.mk sX) m) := ⊥
  let : DiscreteTopology (Tate.Level A_X (Over.mk sX) m ≃ₗ[ZMod m] Tate.Level A_X (Over.mk sX) m) := ⟨rfl⟩
  have : Finite ρL.range := Tate.finite_levelMonodromyImage sL hFinL A hpos (hu n)
  have : Finite ρX.range := Tate.finite_levelMonodromyImage sX hFinX A_X hpos (huX n)
  have hPL : IsPGroup ℓ ρL.range :=
    Tate.primeLevelMonodromyPGroup (Spec (.of L)) Ω' sL hFinL A ℓ hu₁ htrivL n (hu n)
  have hPX : IsPGroup ℓ ρX.range :=
    Tate.primeLevelMonodromyPGroup X Ω' sX hFinX A_X ℓ hx₁ htrivX n (huX n)
  let gL := pathConjugation p g
  obtain ⟨a, ha⟩ := weaklyUnramifiedDvrQuotientLift hKummer W L W' L' i iFrac hiFrac π hπ hiπ ℓ hℓ
    t ρL.range hPL ρL.rangeRestrict
    (Tate.continuous_levelMonodromyToImage sL hFinL A hpos (hu n)) gL
  have hL : ρL (fStar a) = ρL gL := congrArg Subtype.val ha
  have hLq : ρL (fStar (a ^ q)) = ρL (gL ^ q) := by rw [map_pow, map_pow, hL, map_pow]
  obtain ⟨σ, hσ⟩ := hTame B tB htB htB' hregB ℓ hℓB W' L' hjB Ω' t q hq' ρX.range hPX
    ρX.rangeRestrict (Tate.continuous_levelMonodromyToImage sX hFinX A_X hpos (huX n)) a
  let d := ρX σ
  have hX : d * ρX (jStar a) * d⁻¹ = ρX (jStar (a ^ q)) := by
    have hσ' : ρX (σ * jStar a * σ⁻¹) = ρX (jStar a) ^ q := congrArg Subtype.val hσ
    simpa only [map_mul, map_inv, map_pow, d] using hσ'
  obtain ⟨w, hw⟩ := exists_levelPath_intertwiner s sL p A m hpos (hu n)
  obtain ⟨v, hv⟩ := exists_levelChart_intertwiner f j b c hcomm t A₀ A e m hpos
    (hu₀m n) (hu n) (huX n)
  let endS := levelMonodromyZMod s hFin A ℓ hu n
  let endL := levelMonodromyZMod sL hFinL A ℓ hu n
  let endX := levelMonodromyZMod sX hFinX A_X ℓ huX n
  have hP (z : FundamentalGroup s hFin) : w.conj (endS z) = endL (pathConjugation p z) :=
    levelEnd_conj_of_intertwines w _ _ (hw z)
  have hC (z : FundamentalGroup t hFinT) : v.conj (endL (fStar z)) = endX (jStar z) :=
    levelEnd_conj_of_intertwines v _ _ (hv z)
  have hLin : endL (fStar a) = endL gL := congrArg LinearEquiv.toLinearMap hL
  have hLinPow : endL (fStar (a ^ q)) = endL (gL ^ q) := congrArg LinearEquiv.toLinearMap hLq
  have hConj : d.conj (endX (jStar a)) = endX (jStar (a ^ q)) := levelEnd_conj_of_equiv_conj _ _ _ hX
  let eChart := w.trans v
  have hcompare : eChart.conj (endS g) = endX (jStar a) := by
    rw [← LinearEquiv.conj_trans, LinearEquiv.trans_apply, hP, ← hLin, hC]
  have hcomparePow : eChart.conj (endS (g ^ q)) = endX (jStar (a ^ q)) := by
    rw [← LinearEquiv.conj_trans, LinearEquiv.trans_apply, hP, map_pow, ← hLinPow, hC]
  refine ⟨eChart.trans (d.trans eChart.symm), ?_⟩
  change (eChart.trans (d.trans eChart.symm)).conj (endS g) = endS (g ^ q)
  rw [← LinearEquiv.conj_trans, LinearEquiv.trans_apply, hcompare, ← LinearEquiv.conj_trans,
    LinearEquiv.trans_apply, hConj, ← hcomparePow, LinearEquiv.conj_symm_conj]

/-- The three arithmetic inputs suffice for the exact quasi-unipotence proposition. -/
theorem abelianInertiaQuasiUnipotent_of_arithmetic
    (hApprox : ArithmeticRegularLocalApproximationStatement.{u, u, u})
    (hKummer : StrictlyHenselianKummerFactorizationStatement.{u, u})
    (hTame : RegularDivisorTameConjugationStatement.{u, u}) :
    AbelianInertiaQuasiUnipotentStatement.{u} :=
  abelianInertiaQuasiUnipotent_of_powerConjugacy
    (splitInertiaPowerConjugacyReduction (abelianInertiaArithmeticReduction hApprox hKummer hTame))

end Langlands.AbelianScheme
