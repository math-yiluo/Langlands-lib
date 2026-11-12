import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.NecessityGluing
import Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.NecessityRings

/-! # Necessity: vanishing of obstruction cohomology at a versal closed point -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.OpennessOfVersality

open RelativeAffineSections Langlands.Cohomology.ModuleComplex.ObstructionCone PicardGroupoid
open Langlands.AlgebraicGeometry.Deformation Langlands.Algebra

section PointGeneric

open Langlands.CategoryTheory Langlands.Scheme.Modules.LineBundleFlatDescent

variable {C : Type*} [Category C] (G : C ⥤ Scheme.{u})
  {F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}} (Rz : ModuleRealization F)
  {U T : C} {ξ : F.obj (.mk (Opposite.op (G.obj U)))} {η : F.obj (.mk (Opposite.op (G.obj T)))}

/-- If the restriction of a point is the point given by `b` and `ψ`, then the transported
module isomorphism of the point is `ψ`. -/
lemma tr_modIsoR_of_restrict_eq {Z Z' : Over T} (q : Z' ⟶ Z)
    (x : PseudofunctorPointFiber.Points (StackPullback.reindex G F) ξ η Z) (b : Z'.left ⟶ U)
    (hb : q.left ≫ x.1 = b)
    (ψ : (Scheme.Modules.pullback (G.map b)).obj (Rz.mod ξ) ≅
      (Scheme.Modules.pullback (G.map Z'.hom)).obj (Rz.mod η))
    (h : PseudofunctorPointFiber.restrict (StackPullback.reindex G F) ξ η q x = mkPtR G Rz b ψ) :
    tr (G.map q.left) (by rw [← Functor.map_comp, hb]) (by rw [← Functor.map_comp, Over.w q])
      (modIsoR G Rz x).hom = ψ.hom := by
  rw [restrict_eq_of_comp G q x b hb] at h
  have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  rw [← modIsoR_pullIso G Rz q x b hb]
  have h3 : modIsoR G Rz (Z := Z') ⟨b, PseudofunctorPointFiber.pullIso x.2 q.left b Z'.hom hb q.w⟩ =
      modIsoR G Rz (Z := Z') ⟨b, (mkPtR G Rz b ψ).2⟩ := by rw [h2]; rfl
  rw [h3]
  exact congrArg Iso.hom (modIsoR_mkPtR G Rz b ψ)

end PointGeneric

section Necessity

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  [IsProper f] [Flat f]
  {P : Type u} [CommRing P] [Algebra R P] [IsNoetherianRing P]
  (K : (relSpace f P).OrderedAffineCover)
  {A₀ : Type u} [CommRing A₀] [Algebra R A₀] [Algebra P A₀] [IsScalarTower R P A₀]
  [IsNoetherianRing A₀]
  (g : ∀ i j : K.ι, (Γ(relSpace f P, K.U i ⊓ K.U j))ˣ)
  {Q : Type u} [AddCommGroup Q] [Module A₀ Q] [Module P Q] [IsScalarTower P A₀ Q]
  {F : Type u} [AddCommGroup F] [Module A₀ F] [Module P F] [IsScalarTower P A₀ F] [Module R F]

/-- **Necessity.** At a closed point of an affine chart where the family is formally versal,
the obstruction cone has vanishing first cohomology with coefficients in the residue field. -/
theorem hOneVanishes_of_isFormallyVersalAt (hπ : Function.Surjective (algebraMap P A₀))
    (jQ : Q →ₗ[P] P) (hjQinj : Function.Injective jQ)
    (hjQ : ∀ a : P, a ∈ RingHom.ker (algebraMap P A₀) ↔ ∃ x, jQ x = a)
    (hg : ∀ s : K.Idx 2, defect f K g s ∈
      (RingHom.ker (algebraMap P A₀)).map (structureHom f P (K.inter s)).hom)
    (D : Derivation R P F)
    (hD : ∀ (M : Type u) [AddCommGroup M] [Module A₀ M] [Module P M] [IsScalarTower P A₀ M]
      [Module R M] [IsScalarTower R P M] (δ : Derivation R P M),
        ∃ D' : F →ₗ[A₀] M, ∀ x, δ x = D' (D x))
    {L₀ : LineBundle (relSpace f A₀)} (e : ∀ i, Γ(L₀.obj, (testCover f K A₀).U i))
    (he : ∀ i, Scheme.Modules.IsFrameOn (e i) ((testCover f K A₀).U i))
    (hge : CocycleGluing.IsTransition e
      (pushUnits f K (relMap f (IsScalarTower.toAlgHom R P A₀)) (testCover f K A₀).U
        (fun _ _ => le_rfl) g))
    {k : Type u} [Field k] [Algebra R k] (χ₀ : A₀ →ₐ[R] k) (hχ₀ : Function.Surjective χ₀)
    (hv : ArtinianChartVersality.IsFormallyVersalAt f L₀
      (affineBaseMap χ₀ : ArtinianTest.residueBase R k ⟶ affineBase R A₀)) :
    letI : Algebra A₀ k := χ₀.toRingHom.toAlgebra
    HOneVanishes (cplx f K A₀) (dif f K A₀) (deltaMap hπ jQ (hjQ0_of jQ hjQ) D)
      (thetaObs (A₀ := A₀) f K D g) (zObs f K jQ hjQ g hg) k := by
  letI : Algebra A₀ k := χ₀.toRingHom.toAlgebra
  intro c φ hcφ
  -- the `P`-algebra structure of the residue field and the scalar towers
  letI : Algebra P k := ((algebraMap A₀ k).comp (algebraMap P A₀)).toAlgebra
  haveI : IsScalarTower P A₀ k := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R A₀ k := IsScalarTower.of_algebraMap_eq (fun r => (χ₀.commutes r).symm)
  haveI : IsScalarTower R P k := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R k r = χ₀ (algebraMap P A₀ (algebraMap R P r))
    rw [← IsScalarTower.algebraMap_apply, χ₀.commutes])
  have hjQ0 := hjQ0_of jQ hjQ
  -- the Artinian test rings
  obtain ⟨N, hN, hvan⟩ := NecessityRings.exists_pow_vanish jQ φ hjQinj hjQ
  set E := NecessityRings.ExtRing jQ φ N hN hjQ0 with hE
  set qE := NecessityRings.qE R jQ φ N hN hjQ0 with hqE
  set χN := NecessityRings.chiN R A₀ k N with hχN
  set ι := NecessityRings.ι jQ φ N hN hjQ0 with hι
  have hιinj : Function.Injective ι := NecessityRings.ι_injective jQ φ N hN hjQ0 hvan
  have hιr : ∀ a, a ∈ RingHom.ker qE.toRingHom ↔ ∃ t, ι t = a := fun a =>
    ⟨fun ha => NecessityRings.exists_ι_of_qE_eq_zero jQ φ N hN hjQ0 hπ hjQ a ha,
      by rintro ⟨t, rfl⟩; exact NecessityRings.qE_ι jQ φ N hN hjQ0 t⟩
  have hιsq : ∀ t t', ι t * ι t' = 0 := NecessityRings.ι_mul_ι jQ φ N hN hjQ0
  have hqρ : qE.comp (IsScalarTower.toAlgHom R P E) = χN.comp (IsScalarTower.toAlgHom R P A₀) :=
    NecessityRings.qE_comp jQ φ N hN hjQ0
  have hqsurj : Function.Surjective qE := NecessityRings.qE_surjective jQ φ N hN hjQ0 hπ
  -- `φ` is the obstruction map of the extension
  have hφ : phiQ χN qE hqρ hπ jQ hjQ0 ι hιinj hιr = φ := by
    ext x
    apply hιinj
    rw [jM_phiQ]
    exact NecessityRings.algebraMap_jQ jQ φ N hN hjQ0 x
  rw [← hφ] at hcφ
  -- the glued deformation over the extension ring
  obtain ⟨Nb, fN, hfN, φy, hfN_trans, hφy⟩ := exists_deformation f K g χN qE hqρ ι hιr hιsq hπ
    jQ hjQ hg hqsurj hιinj c hcφ e he hge
  -- the Artinian tests and the point over the base test
  let BT := NecessityRings.baseTest R N hN hχ₀ (A₀ := A₀) (k := k)
  let AT := NecessityRings.extTest R jQ φ N hN hjQ0 hχ₀ hπ
  let qT : AT ⟶ BT := NecessityRings.qTest R jQ φ N hN hjQ0 hχ₀ hπ
  let y : ArtinianChartVersality.FiberPoints f L₀ Nb (Over.mk (ArtinianTest.baseMap qT)) :=
    mkPtR (relativeSpace f) PicardGroupoid.moduleRealization (ξ := Core.mk L₀) (η := Core.mk Nb)
      (Z := Over.mk (ArtinianTest.baseMap qT)) (affineBaseMap χN) φy
  have hy : ArtinianTest.reduction BT ≫ y.1 = affineBaseMap χ₀ := by
    change ArtinianTest.reduction BT ≫ affineBaseMap χN = _
    rw [reduction_comp_affineBaseMap]
    rfl
  -- versality gives a point over the identity test
  have hlift := (ArtinianChartTestReduction.hasLiftingForAt_iff_base f L₀ _ qT).mp
    (hv qT hqsurj)
  obtain ⟨⟨bx, ex⟩, hx⟩ := hlift Nb y hy
  obtain ⟨χ', rfl⟩ := exists_affineBaseMap_eq (R := R) (A := A₀) (B := E) bx
  -- the lift of the chart map
  have hbase : (ArtinianChartLifting.testArrow qT (Category.comp_id _)).left ≫ affineBaseMap χ' =
      affineBaseMap χN := congrArg Sigma.fst hx
  have hχ' : qE.comp χ' = χN := by
    apply affineBaseMap_injective
    rw [affineBaseMap_comp]
    exact hbase
  -- the lifted isomorphism and its transport
  let ψ := modIso f (⟨affineBaseMap χ', ex⟩ :
    ArtinianChartVersality.FiberPoints f L₀ Nb (Over.mk (𝟙 (ArtinianTest.base AT))))
  let ψ₁ := ψ ≪≫ (Scheme.Modules.pullbackCongr ((relativeSpace f).map_id _)).app Nb.obj
  have htr : Langlands.Scheme.Modules.LineBundleFlatDescent.tr (relMap f qE)
      (by rw [← relMap_comp, hχ']) (Category.comp_id _) ψ₁.hom = φy.hom := by
    rw [Iso.trans_hom, Iso.app_hom, tr_comp_pullbackCongr]
    exact tr_modIsoR_of_restrict_eq (relativeSpace f) PicardGroupoid.moduleRealization
      (ArtinianChartLifting.testArrow qT (Category.comp_id _)) _ (affineBaseMap χN) hbase φy hx
  -- the derivation `χ' ∘ π - ρ'` and its factorization through `D`
  obtain ⟨δ'', hδ''⟩ := exists_derivation_of_lift χN qE hqρ ι hιr hιsq hιinj χ' hχ'
  obtain ⟨D'', hD''⟩ := hD k δ''
  have hχ'comp : χ'.comp (IsScalarTower.toAlgHom R P A₀) = rhoCorr ι hιsq D'' D := by
    ext p
    rw [rhoCorr_apply, ← hD'' p, hδ'' p]
    change _ = algebraMap P E p + (_ - algebraMap P E p)
    ring
  obtain ⟨b, hb⟩ := exists_b_of_lift f K g χN qE hqρ ι hιr hιsq hqsurj hιinj c e he hge Nb fN hfN
    hfN_trans φy hφy D'' D χ' hχ' hχ'comp ψ₁ htr
  refine ⟨b, D'', hb, ?_⟩
  ext x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, deltaMap_apply, LinearMap.zero_apply]
  apply hιinj
  rw [map_add, map_zero, ← hD'' (jQ x), hδ'' (jQ x)]
  have h1 : (χ'.comp (IsScalarTower.toAlgHom R P A₀)) (jQ x) = 0 := by
    change χ' (algebraMap P A₀ (jQ x)) = 0
    rw [hjQ0 x, map_zero]
  have h2 : (IsScalarTower.toAlgHom R P E) (jQ x) = ι (φ x) :=
    NecessityRings.algebraMap_jQ jQ φ N hN hjQ0 x
  rw [h1, h2]
  abel

end Necessity

end Langlands.AlgebraicGeometry.Picard.OpennessOfVersality
