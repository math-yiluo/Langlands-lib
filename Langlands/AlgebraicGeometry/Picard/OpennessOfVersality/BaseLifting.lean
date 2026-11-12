import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Sufficiency
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.PointModule
import Langlands.AlgebraicGeometry.Picard.ArtinianChartTestReduction

/-! # Base lifting at points of an affine chart from vanishing obstruction cohomology -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open RelativeAffineSections Langlands.Scheme.Modules.LineBundleFlatDescent

section Helpers

/-- Every arrow between affine bases over `Spec R` comes from an `R`-algebra homomorphism. -/
lemma exists_affineBaseMap_eq {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (b : affineBase R B ⟶ affineBase R A) :
    ∃ χ : A →ₐ[R] B, affineBaseMap χ = b := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective b.left
  have hw : b.left ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := Over.w b
  rw [← hφ, ← Spec.map_comp] at hw
  have hcomm := congrArg CommRingCat.Hom.hom (Spec.map_injective hw)
  refine ⟨{ φ.hom with commutes' := fun r => congrArg (fun h : R →+* B => h r) hcomm }, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom _) = b.left
  rw [← hφ]
  rfl

/-- Transport absorbs a change of the target pullback along an equality of morphisms. -/
lemma tr_comp_pullbackCongr {Z Z' A₁ B₁ : Scheme.{u}} {C : A₁.Modules} {D : B₁.Modules}
    (k : Z' ⟶ Z) {u : Z ⟶ A₁} {v₁ v₂ : Z ⟶ B₁} {u' : Z' ⟶ A₁} {v' : Z' ⟶ B₁}
    (hu : k ≫ u = u') (hv₁ : k ≫ v₁ = v') (hv₂ : k ≫ v₂ = v') (e : v₁ = v₂)
    (φ : (Scheme.Modules.pullback u).obj C ⟶ (Scheme.Modules.pullback v₁).obj D) :
    tr k hu hv₂ (φ ≫ (Scheme.Modules.pullbackCongr e).hom.app D) = tr k hu hv₁ φ := by
  subst e
  simp [Scheme.Modules.pullbackCongr]

end Helpers

section PointGeneric

open Langlands.CategoryTheory PicardGroupoid

variable {C : Type*} [Category C] (G : C ⥤ Scheme.{u})
  {F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}} (Rz : ModuleRealization F)
  {U T : C} {ξ : F.obj (.mk (Opposite.op (G.obj U)))} {η : F.obj (.mk (Opposite.op (G.obj T)))}

/-- A point given by a base map and a module isomorphism restricts to a given point as soon as
the base maps are compatible and the transported module isomorphism is the one of the given
point. -/
lemma restrict_mkPtR_eq {Z Z' : Over T} (q : Z' ⟶ Z) (a : Z.left ⟶ U)
    (ψ : (Scheme.Modules.pullback (G.map a)).obj (Rz.mod ξ) ≅
      (Scheme.Modules.pullback (G.map Z.hom)).obj (Rz.mod η))
    (y : PseudofunctorPointFiber.Points (StackPullback.reindex G F) ξ η Z')
    (hb : q.left ≫ a = y.1)
    (h : tr (G.map q.left) (by rw [← Functor.map_comp, hb]) (by rw [← Functor.map_comp, Over.w q])
      ψ.hom = (modIsoR G Rz y).hom) :
    PseudofunctorPointFiber.restrict (StackPullback.reindex G F) ξ η q (mkPtR G Rz a ψ) = y := by
  rcases y with ⟨b, ey⟩
  rw [restrict_eq_of_comp G q (mkPtR G Rz a ψ) b hb]
  rw [← mkPtR_modIsoR G Rz ⟨b, ey⟩]
  conv_lhs => rw [← mkPtR_modIsoR G Rz ⟨b, _⟩]
  congr 1
  apply Iso.ext
  rw [modIsoR_pullIso G Rz q (mkPtR G Rz a ψ) b hb]
  rw [modIsoR_mkPtR]
  exact h

end PointGeneric

section Kernel

variable {A B : Type u} [CommRing A] [CommRing B] (q : A →+* B) (hq : Function.Surjective q)
  (hsq : ∀ a ∈ RingHom.ker q, ∀ b ∈ RingHom.ker q, a * b = 0)

include hsq in
/-- A square-zero kernel is killed by itself. -/
lemma isTorsionBySet_ker : Module.IsTorsionBySet A (RingHom.ker q) (RingHom.ker q) := by
  intro m a
  apply Subtype.ext
  exact hsq a a.2 m m.2

/-- The kernel of a surjection with square-zero kernel, as a module over the target. -/
abbrev kerModule : Module B (RingHom.ker q) :=
  letI := (isTorsionBySet_ker q hsq).module
  Module.compHom (RingHom.ker q) (RingHom.quotientKerEquivOfSurjective hq).symm.toRingHom

/-- The target acts on the kernel through any preimage. -/
lemma kerModule_smul (a : A) (m : RingHom.ker q) :
    (kerModule q hq hsq).smul (q a) m = a • m := by
  letI := (isTorsionBySet_ker q hsq).module
  change (RingHom.quotientKerEquivOfSurjective hq).symm (q a) • m = a • m
  rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
  rfl

end Kernel

section Wrapper

open Langlands.Cohomology.ModuleComplex.ObstructionCone PicardGroupoid
open Langlands.AlgebraicGeometry.Deformation

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  [IsSeparated f] [Flat f]
  {P : Type u} [CommRing P] [Algebra R P] (K : (relSpace f P).OrderedAffineCover)
  {A₀ : Type u} [CommRing A₀] [Algebra R A₀] [Algebra P A₀] [IsScalarTower R P A₀]
  (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
  {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module P Q] [IsScalarTower P A₀ Q]
  {F : Type u} [AddCommGroup F] [Module A₀ F] [Module P F] [IsScalarTower P A₀ F] [Module R F]

/-- **Base lifting on an affine chart.** If the obstruction cone has vanishing first cohomology
with coefficients in the kernel of a square-zero surjection of Artinian tests (for every chart
map compatible with the point `p`), then the chart family has base lifting at `p` along it. -/
theorem hasBaseLiftingForAt_of_HOneVanishes (hπ : Function.Surjective (algebraMap P A₀))
    (jQ : Q →ₗ[P] P) (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom)
    (D : Derivation R P F)
    {L₀ : LineBundle (relSpace f A₀)} (e : ∀ i, Γ(L₀.obj, (testCover f K A₀).U i))
    (he : ∀ i, Scheme.Modules.IsFrameOn (e i) ((testCover f K A₀).U i))
    (hge : CocycleGluing.IsTransition e
      (pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀)) (testCover f K A₀).U
        (fun _ _ => le_rfl) g))
    {K' : Type u} [Field K'] [Algebra R K'] (p : ArtinianTest.residueBase R K' ⟶ affineBase R A₀)
    {A B : ArtinianTest R K'} (q : A ⟶ B)
    (hq : Function.Surjective (ArtinianTest.toAlgHom q))
    (hsq : ∀ a ∈ RingHom.ker (ArtinianTest.toAlgHom q).toRingHom,
      ∀ b ∈ RingHom.ker (ArtinianTest.toAlgHom q).toRingHom, a * b = 0)
    (hP : ∀ χ : A₀ →ₐ[R] B.algebra, ∃ ρ : P →ₐ[R] A.algebra,
      (ArtinianTest.toAlgHom q).comp ρ = χ.comp (IsScalarTower.toAlgHom R P A₀))
    (hH : ∀ χ : A₀ →ₐ[R] B.algebra, ArtinianTest.reduction B ≫ affineBaseMap χ = p →
      ∀ (M : Type u) [AddCommGroup M] [Module B.algebra M] [Module A₀ M],
        (∀ (a : A₀) (m : M), a • m = χ a • m) →
        HOneVanishes (cplx f K A₀) (dif f K A₀) (deltaMap hπ jQ (hjQ0_of jQ hjQ) D)
          (thetaObs (A₀ := A₀) f K D g) (zObs f K jQ hjQ g hg) M) :
    ArtinianChartTestReduction.HasBaseLiftingForAt f L₀ p q := by
  intro N y hy
  rcases y with ⟨b, ey⟩
  obtain ⟨χ, rfl⟩ := exists_affineBaseMap_eq (R := R) (A := A₀) (B := B.algebra) b
  obtain ⟨ρ, hρ⟩ := hP χ
  set qA := ArtinianTest.toAlgHom q with hqA
  letI : Algebra P A.algebra := ρ.toRingHom.toAlgebra
  haveI : IsScalarTower R P A.algebra :=
    IsScalarTower.of_algebraMap_eq (fun r => (ρ.commutes r).symm)
  have hqρ : qA.comp (IsScalarTower.toAlgHom R P A.algebra) =
      χ.comp (IsScalarTower.toAlgHom R P A₀) := by
    ext x
    exact DFunLike.congr_fun hρ x
  -- the kernel as a module
  let M := RingHom.ker qA.toRingHom
  letI mB : Module B.algebra M := kerModule qA.toRingHom hq hsq
  letI mA : Module A₀ M := Module.compHom M χ.toRingHom
  haveI : IsScalarTower P A₀ M := ⟨fun p a m => by
    obtain ⟨a', ha'⟩ := hq (χ a)
    have ha'' : qA.toRingHom a' = χ a := ha'
    have h1 : χ (p • a) = qA.toRingHom (ρ p * a') := by
      rw [map_mul, ha'', Algebra.smul_def, map_mul]
      congr 1
      exact (DFunLike.congr_fun hρ p).symm
    have e1 : (p • a) • m = (ρ p * a') • m := by
      change (kerModule qA.toRingHom hq hsq).smul (χ (p • a)) m = _
      rw [h1, kerModule_smul]
    have e2 : a • m = a' • m := by
      change (kerModule qA.toRingHom hq hsq).smul (χ a) m = _
      rw [← ha'', kerModule_smul]
    rw [e1, e2, mul_smul]
    rfl⟩
  let jM : M →ₗ[P] A.algebra :=
    { toFun := Subtype.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hn : IsNilpotent (RingHom.ker qA.toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.mpr fun a ha c hc => ?_
    rw [hsq a ha c hc]
    exact Submodule.zero_mem _
  have hH' := hH χ hy M (fun _ _ => rfl)
  obtain ⟨χ', hχ', ψ, htr⟩ := exists_lift f K g χ qA hqρ hπ jQ hjQ hg D e he hge hq hn jM
    Subtype.val_injective (fun a => ⟨fun h => ⟨⟨a, h⟩, rfl⟩, by rintro ⟨m, rfl⟩; exact m.2⟩)
    (fun m m' => hsq _ m.2 _ m'.2) hH' N
    (modIso f (⟨affineBaseMap χ, ey⟩ :
      ArtinianChartVersality.FiberPoints f L₀ N (Over.mk (ArtinianTest.baseMap q))))
  have hb : ArtinianTest.baseMap q ≫ affineBaseMap χ' = affineBaseMap χ := by
    rw [← hχ', affineBaseMap_comp]
    rfl
  refine ⟨mkPtR (relativeSpace f) moduleRealization (ξ := Core.mk L₀) (η := Core.mk N)
    (Z := Over.mk (𝟙 (ArtinianTest.base A))) (affineBaseMap χ')
    (ψ ≪≫ (Scheme.Modules.pullbackCongr ((relativeSpace f).map_id _).symm).app N.obj), ?_⟩
  exact restrict_mkPtR_eq (relativeSpace f) moduleRealization
    (ArtinianChartLifting.testArrow q (Category.comp_id _)) (affineBaseMap χ') _
    ⟨affineBaseMap χ, ey⟩ hb ((tr_comp_pullbackCongr _ _ _ _ _ _).trans htr)

end Wrapper

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
