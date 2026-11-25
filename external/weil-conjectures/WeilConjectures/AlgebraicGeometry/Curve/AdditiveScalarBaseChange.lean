/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing


public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveCohomologyLinearBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism

/-! # Scalar-compatible flat base change for additive first cohomology -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

/-- For a sheaf `G` identified with the additive sheaf of `C`, multiplication of sections by the
images of scalars `c : k` gives sheaf endomorphisms `μ_c` of `G`, and these make the first
cohomology `H¹(G)` a `k`-module on which `μ_c` acts as `c •`. -/
theorem exists_additive_cohomology_scalar_action
    {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k))
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x)) :
    let T := Sheaf.functorH.{u + 1} C.smallEtaleTopology 1
    ∃ m : Module k (T.obj G),
      let := m
      ∀ c : k, ∃ μ : G ⟶ G,
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) ∧
        ∀ x : T.obj G, T.map μ x = c • x := by
  classical
  let T := Sheaf.functorH.{u + 1} C.smallEtaleTopology 1
  let ρ (U : C.Etaleᵒᵖ) : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
  have hρ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (c : k) :
      g.unop.left.appTop.hom (ρ U c) = ρ V c := by
    dsimp [ρ]
    have hw : g.unop.left ≫ U.unop.hom = V.unop.hom := g.unop.w
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hw]
  let μ (c : k) : G ⟶ G := ⟨{
    app U := AddCommGrpCat.ofHom {
      toFun x := (a U).symm (a U x * ρ U c)
      map_zero' := by simp
      map_add' x y := by simp [add_mul] }
    naturality U V g := by
      ext x
      apply (a V).injective
      change a V ((a V).symm (a V (G.obj.map g x) * ρ V c)) =
        a V (G.obj.map g ((a U).symm (a U x * ρ U c)))
      simp only [AddEquiv.apply_symm_apply, ha U V g]
      rw [g.unop.left.appTop.hom.map_mul, hρ] }⟩
  have hμ (c : k) (U : C.Etaleᵒᵖ) (x : G.obj.obj U) :
      a U ((μ c).hom.app U x) = a U x * ρ U c := by
    exact (a U).apply_symm_apply _
  have hzero : μ 0 = 0 := by
    apply Sheaf.hom_ext
    ext U x
    apply (a U).injective
    rw [hμ]
    simp
  have hone : μ 1 = 𝟙 G := by
    apply Sheaf.hom_ext
    ext U x
    apply (a U).injective
    rw [hμ]
    simp
  have hadd (c d : k) : μ (c + d) = μ c + μ d := by
    apply Sheaf.hom_ext
    ext U x
    apply (a U).injective
    change a U ((μ (c + d)).hom.app U x) =
      a U ((μ c).hom.app U x + (μ d).hom.app U x)
    rw [map_add, hμ, hμ, hμ, map_add, mul_add]
  have hmul (c d : k) : μ (c * d) = μ d ≫ μ c := by
    apply Sheaf.hom_ext
    ext U x
    apply (a U).injective
    change a U ((μ (c * d)).hom.app U x) =
      a U ((μ c).hom.app U ((μ d).hom.app U x))
    rw [hμ, hμ, hμ, map_mul]
    ring
  let m : Module k (T.obj G) := {
    smul c x := T.map (μ c) x
    one_smul x := by
      change T.map (μ 1) x = x
      rw [hone, T.map_id]
      rfl
    mul_smul c d x := by
      change T.map (μ (c * d)) x = T.map (μ c) (T.map (μ d) x)
      rw [hmul, T.map_comp]
      rfl
    smul_zero c := (T.map (μ c)).hom.map_zero
    smul_add c x y := (T.map (μ c)).hom.map_add x y
    zero_smul x := by
      change T.map (μ 0) x = 0
      rw [hzero, T.map_zero]
      rfl
    add_smul c d x := by
      change T.map (μ (c + d)) x = T.map (μ c) x + T.map (μ d) x
      rw [hadd, T.map_add]
      rfl }
  let := m
  have hscalar : ∀ c : k, ∃ μ' : G ⟶ G,
      (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a U (μ'.hom.app U x) = a U x * ρ U c) ∧
      ∀ x : T.obj G, T.map μ' x = c • x := by
    intro c
    exact ⟨μ c, hμ c, fun _ ↦ rfl⟩
  exact ⟨m, hscalar⟩



/-- The first cohomology comparison for additive structure sheaves preserves scalars
and the canonical base-change map. No Frobenius or constant-sheaf assertion is made.
Source: Stacks Project, Tags 0A3P (first sentence of proof), 02KH (flat base change),
03P2 (quasi-coherent comparison), and 02O6 (proper coherent finiteness).
(blueprint: lem-pbc-additive-scalar-base-change)

Proof: The natural section equivalences identify G and G' with the lifted additive
structure sheaves. Multiplication by the structural image of c is additive and
commutes with restriction, so defines μ on each sheaf. Applying additive cohomology
to the zero, identity, sum and product relations supplies the actual scalar action
on H¹. Compare it with coherent H¹(C,O_C) using the etale/Zariski comparison;
proper coherent finiteness makes the resulting k-module V finite-dimensional.
On the base change, use the same comparison and the canonical flat base-change
isomorphism, with tensor factors interchanged, to obtain b'. The two scalar actions
agree with multiplication on coherent cohomology by naturality in module maps.
For the last formula, compute on a finite affine cover of C and its pulled-back
cover. The adjoint section formula for q says precisely that its cochain map is
structural pullback, hence is s ↦ 1 tensor s under the affine-section tensor
identifications. Flat tensor product preserves kernels and images. The Cech
comparison therefore induces the displayed equality on H¹, in the specified Ext
model, using the natural Ext/derived comparison. If C has dimension zero,
coherent H¹ is zero and all these formulas still hold. This argument uses neither
Artin--Schreier exactness nor semilinear Frobenius invariance. -/
theorem exists_additive_scalar_base_change
    {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f] [Smooth f] [ConnectedSpace C] [IsProper f]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (G : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G' : Sheaf C'.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : C.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (a' : ∀ U : C'.Etaleᵒᵖ, G'.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : C.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (ha' : ∀ (U V : C'.Etaleᵒᵖ) (g : U ⟶ V) (x : G'.obj.obj U),
      a' V (G'.obj.map g x) = g.unop.left.appTop (a' U x))
    (q : (Etale.upperStar AddCommGrpCat.{u + 1} ι').obj G ⟶ G')
    (hq : (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        a' (Opposite.op ((MorphismProperty.Over.pullback @Etale ⊤ ι').obj U.unop))
          (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι').homEquiv
            G G' q).hom.app U x) =
          (Limits.pullback.fst U.unop.hom ι').appTop (a U x))) :
    ∃ (V : ModuleCat.{u + 1} k) (_ : FiniteDimensional k V)
      (b : Sheaf.H G 1 ≃+ V) (b' : Sheaf.H G' 1 ≃+ (k' ⊗[k] V)),
      (∀ c : k, ∃ μ : G ⟶ G,
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) ∧
        ∀ x : Sheaf.H G 1,
          b (Sheaf.H.map μ 1 x) = c • b x) ∧
      (∀ c : k', ∃ μ : G' ⟶ G',
        (∀ (U : C'.Etaleᵒᵖ) (x : G'.obj.obj U),
          let ρ : k' →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f'.appTop.hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom)
          a' U (μ.hom.app U x) = a' U x * ρ c) ∧
        ∀ x : Sheaf.H G' 1,
          b' (Sheaf.H.map μ 1 x) = c • b' x) ∧
      ∀ x, b' (Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x)) = 1 ⊗ₜ[k] b x := by
  classical
  obtain ⟨m, hscalar⟩ := exists_additive_cohomology_scalar_action f G a ha
  obtain ⟨m', hscalar'⟩ := exists_additive_cohomology_scalar_action f' G' a' ha'
  let : Module k (Sheaf.H G 1) := m
  let : Module k' (Sheaf.H G' 1) := m'
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let T := DerivedCategory.singleFunctor
    (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
  obtain ⟨α⟩ := Scheme.nonempty_sheafH_extDerivedIso C 1
  obtain ⟨d, hd⟩ := exists_addEquiv_etaleCohomology_one_structureSheaf f G a ha
  let e : Sheaf.H G 1 ≃+
      Scheme.Modules.H (SheafOfModules.unit C.ringCatSheaf) 1 :=
    (α.app G).addCommGroupIsoToAddEquiv.trans d
  let L : Sheaf.H G 1 →ₗ[k]
      Scheme.Modules.H (SheafOfModules.unit C.ringCatSheaf) 1 :=
    { e.toAddMonoidHom with
      map_smul' c x := by
        obtain ⟨μ, hμ, hmap⟩ := hscalar c
        rw [← hmap x]
        change d ((α.hom.app G) (Sheaf.H.map μ 1 x)) = c • e x
        have hn := congrArg (fun t ↦ t x) (α.hom.naturality μ)
        change (α.hom.app G) (Sheaf.H.map μ 1 x) =
          T.map μ ((α.hom.app G) x) at hn
        rw [hn]
        exact hd c μ hμ _ }
  have : IsProper (C ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : (SheafOfModules.unit C.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf)
  have : (SheafOfModules.unit C.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit C.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (SheafOfModules.unit C.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have := Scheme.Modules.finiteDimensional_H_of_isProper (k := k)
    (SheafOfModules.unit C.ringCatSheaf) 1
  have hfin : FiniteDimensional k (Sheaf.H G 1) :=
    FiniteDimensional.of_injective L e.injective
  obtain ⟨e', he'⟩ := exists_additive_cohomology_linear_base_change
    f h G G' a a' ha ha' q hq hscalar hscalar'
  refine ⟨ModuleCat.of k (Sheaf.H G 1), hfin, AddEquiv.refl _, e'.toAddEquiv,
    ?_, ?_, ?_⟩
  · exact hscalar
  · intro c
    obtain ⟨μ, hμ, hmap⟩ := hscalar' c
    refine ⟨μ, hμ, ?_⟩
    intro x
    change ∀ x : Sheaf.H G' 1, Sheaf.H.map μ 1 x = c • x at hmap
    change e' (Sheaf.H.map μ 1 x) = c • e' x
    rw [hmap x]
    exact e'.map_smul c x
  · exact he'


end AlgebraicGeometry.IsCurve
