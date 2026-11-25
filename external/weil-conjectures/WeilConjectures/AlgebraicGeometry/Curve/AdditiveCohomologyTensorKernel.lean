/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveCohomologyBaseChangeSquare
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologySeparated

/-! # Kernel of additive cohomology tensor pullback -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

/-- The tensor-linear extension of canonical additive pullback has trivial kernel.
Source: Stacks Project, Tags 02KH (finite affine cover proof) and 03P2.
(blueprint: lem-pbc-additive-cohomology-tensor-kernel)

Proof: IsCurve makes C quasi-compact and separated. Choose a finite affine open
cover and its inverse-image cover on C'. Finite intersections and their base
changes are affine. The natural coordinates identify G and G' with the lifted
associated structure sheaves. Their scalar endomorphisms are uniquely fixed by
the section formulas, so the scalar-natural coefficient and etale/Zariski
comparisons identify the specified cohomology actions with structural scalars.
Compute both cohomology groups using the chosen covers. Affine section base change
identifies the latter Cech complex with k' tensor the former; the section formula
hq identifies the map on cochains with x mapping to 1 tensor x. Naturality of the
Cech-to-cohomology comparison identifies the induced map with H(q) after the
canonical Ext cohomology pullback. Pure tensors generate, so hβ identifies β
with the induced scalar-extension map.
For injectivity, tensoring over k is exact and identifies the cycles and the
boundaries of the tensor complex with the tensors of the original cycles and
boundaries. Thus its homology is the tensor of the original homology. A class z
with β z = 0 corresponds to a tensor-cycle which is a tensor-boundary, and hence
z = 0 in tensor homology. Transporting back gives the claimed kernel equality.
The displayed pullback is transported to the categorical pullback by its unique
isomorphism. Empty and affine schemes have zero first cohomology, so the argument
also covers those cases. No properness or finite-dimensionality is used. -/
theorem additive_cohomology_tensor_kernel
    {k k' : Type u}
    [Field k] [Field k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f]
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
          (Limits.pullback.fst U.unop.hom ι').appTop (a U x)))
    [Module k (Sheaf.H G 1)] [Module k' (Sheaf.H G' 1)]
    (hscalar : ∀ c : k, ∃ μ : G ⟶ G,
        (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
          let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
          a U (μ.hom.app U x) = a U x * ρ c) ∧
        ∀ x : Sheaf.H G 1,
          Sheaf.H.map μ 1 x = c • x)
    (hscalar' : ∀ c : k', ∃ μ : G' ⟶ G',
        (∀ (U : C'.Etaleᵒᵖ) (x : G'.obj.obj U),
          let ρ : k' →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
            (f'.appTop.hom.comp (Scheme.ΓSpecIso (.of k')).inv.hom)
          a' U (μ.hom.app U x) = a' U x * ρ c) ∧
        ∀ x : Sheaf.H G' 1,
          Sheaf.H.map μ 1 x = c • x)
    (β : (k' ⊗[k] Sheaf.H G 1) →ₗ[k'] Sheaf.H G' 1)
    (hβ : ∀ (b : k') (x : Sheaf.H G 1),
      β (b ⊗ₜ[k] x) = b • Sheaf.H.map q 1 (Etale.cohomologyMap ι' G 1 x)) :
    ∀ z, β z = 0 → z = 0 := by
  classical
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨e, e', he⟩ := Scheme.Modules.exists_additive_cohomology_baseChange_square
    f h 1 G G' a a' ha ha' q hq hscalar hscalar'
  let t := TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl k' k') e
  let M := SheafOfModules.unit C.ringCatSheaf
  let : M.IsQuasicoherent := SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf)
  have hcomm : e'.toLinearMap.comp β =
      (Scheme.Modules.H.baseChange (S := k') f M 1).comp t.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hβ, map_smul, he]
    rfl
  have hinj := (Scheme.Modules.H.baseChange_bijective_of_isSeparated
    (S := k') f M 1).injective
  intro z hz
  apply t.injective
  apply hinj
  have hc := LinearMap.congr_fun hcomm z
  change e' (β z) = Scheme.Modules.H.baseChange (S := k') f M 1 (t z) at hc
  simpa only [hz, map_zero] using hc.symm


end AlgebraicGeometry.IsCurve
