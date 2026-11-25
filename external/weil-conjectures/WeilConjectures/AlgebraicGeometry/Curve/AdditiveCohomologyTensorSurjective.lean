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

/-! # Surjectivity of additive cohomology tensor pullback -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

/-- The tensor-linear extension of canonical additive pullback is surjective.
Source: Stacks Project, Tags 02KH (finite affine cover proof) and 03P2.
(blueprint: lem-pbc-additive-cohomology-tensor-surjective)

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
For surjectivity, represent a target class by a cocycle of the pulled-back
complex. In the tensor complex it is a cycle. Exactness of tensoring over k
identifies its cycle module with k' tensor the original cycle module. Express it
as a finite sum of pure tensors of original cycles. Their original cohomology
classes give z in k' tensor H¹(G), and the cochain formula gives β z equal to the
prescribed target class. This proves surjectivity.
The displayed pullback is transported to the categorical pullback by its unique
isomorphism. Empty and affine schemes have zero first cohomology, so the argument
also covers those cases. No properness or finite-dimensionality is used. -/
theorem additive_cohomology_tensor_surjective
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
    Function.Surjective β := by
  classical
  let M := SheafOfModules.unit C.ringCatSheaf
  let : M.IsQuasicoherent := SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf)
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨e, e', he⟩ := Scheme.Modules.exists_additive_cohomology_baseChange_square
    f h 1 G G' a a' ha ha' q hq hscalar hscalar'
  let t : (k' ⊗[k] Sheaf.H G 1) ≃ₗ[k'] (k' ⊗[k] Scheme.Modules.HOver f M 1) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl k' k') e
  let B := Scheme.Modules.H.baseChange (S := k') f M 1
  have hcomm (z : k' ⊗[k] Sheaf.H G 1) : e' (β z) = B (t z) := by
    induction z using TensorProduct.inductionOn with
    | tmul b x =>
      rw [hβ, e'.map_smul, he]
      change b • Scheme.Modules.H.baseChangeLinear (S := k') f M 1 (e x) =
        B (b ⊗ₜ[k] e x)
      rfl
    | add z w hz hw => simp only [map_add, hz, hw]
  intro y
  obtain ⟨z, hz⟩ :=
    (Scheme.Modules.H.baseChange_bijective_of_isSeparated (S := k') f M 1).surjective
      (e' y)
  refine ⟨t.symm z, e'.injective ?_⟩
  rw [hcomm, t.apply_symm_apply, hz]

end AlgebraicGeometry.IsCurve
