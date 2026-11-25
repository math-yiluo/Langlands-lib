/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist
public import WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension
public import WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel
public import WeilConjectures.WeilSheaf.DualIrreducible

/-!
# Nonexceptionality of the dual

The geometric irreducible constituents of the dual `M^∨` of a lisse sheaf `M` are the duals of
those of `M` (`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_constituent_of_constituent_dual`),
and the dual of the linear Artin–Schreier sheaf `ℒ_{ψ⁻¹(a x)}` is `ℒ_{ψ(a x)}`
(`AlgebraicGeometry.nonempty_iso_dual_artinSchreier`, the pullback of the dual of a lisse sheaf
being the dual of the pullback). Hence if `M` is nonexceptional for `ψ`, then `M^∨` is
nonexceptional for `ψ⁻¹`, and so is the twisted dual `M^∨ ⊗ 𝓑_b`, which is moreover irreducible
lisse if `M` is. (blueprint: `proposition-purity-lisse-part-fourier-transform`, part (2))

## Main statements

- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isNonexceptional_dual`.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isIrreducibleLisse_twistedDual` and
  `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isNonexceptional_twistedDual`.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The geometric fiber of the affine line is irreducible. -/
instance affineLine.irreducibleSpace_geometricFiber :
    IrreducibleSpace (affineLine k₀ ↘ Spec (.of k₀)).geometricFiber := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have : UniversallyOpen (affineLine k₀ ↘ Spec (.of k₀)) := by
    have := SmoothOfRelativeDimension.smooth 1 (affineLine k₀ ↘ Spec (.of k₀))
    infer_instance
  have : IrreducibleSpace (Scheme.specAlgebraicClosure k₀).left :=
    inferInstanceAs (IrreducibleSpace (Spec (.of (AlgebraicClosure k₀))))
  exact inferInstanceAs (IrreducibleSpace ↥(pullback (C := Scheme.{u})
    (affineLine k₀ ↘ Spec (.of k₀)) (Scheme.specAlgebraicClosure k₀).hom))

namespace WeilSheaf.LisseOnDenseOpen

/-- If the lisse sheaf `M` of `D` is nonexceptional for `ψ`, its dual `M^∨` is nonexceptional
for `ψ⁻¹`: a geometric constituent `ℒ_{ψ⁻¹(a x)}|_U` of `M^∨` would dualise to the geometric
constituent `ℒ_{ψ(a x)}|_U` of `M`. (blueprint: `proposition-purity-lisse-part-fourier-transform`,
part (2)) -/
theorem isNonexceptional_dual (D : LisseOnDenseOpen k₀ l) {ψ : AddChar k₀ (PadicAlgCl l)}
    (h : D.sheaf.IsNonexceptional ψ D.j) : (D.sheaf.dual D.lisse).IsNonexceptional ψ⁻¹ D.j := by
  rintro a ⟨B, i, p, hB, hi, hp⟩
  refine h a ?_
  let jbar := Scheme.Hom.geometricFiberMap D.j (comp_over D.j (Spec (CommRingCat.of k₀)))
  let sa := affineLine.geometricSMul k₀ a
  have hL : ProEtale.IsAdicLisseSheaf ((sa)^*ᵃ[l].obj (artinSchreier ψ⁻¹ 1).obj.carrier) :=
    ProEtale.IsAdicLisseSheaf.upperStar sa (isLisse_artinSchreier ψ⁻¹ 1)
  obtain ⟨B', i', p', hB', hi', hp'⟩ :=
    D.lisse.exists_constituent_of_constituent_dual hB (hL.upperStar jbar) i p
  obtain ⟨E⟩ := nonempty_iso_dual_artinSchreier ψ⁻¹ (1 : k₀)
  rw [inv_inv] at E
  have := ProEtale.isIso_adicUpperStarDualComparison jbar hL
  have := ProEtale.isIso_adicUpperStarDualComparison sa (isLisse_artinSchreier ψ⁻¹ 1)
  let e := (asIso (ProEtale.adicUpperStarDualComparison l jbar
      ((sa)^*ᵃ[l].obj (artinSchreier ψ⁻¹ 1).obj.carrier))).symm ≪≫
    (jbar)^*ᵃ[l].mapIso ((asIso (ProEtale.adicUpperStarDualComparison l sa
      (artinSchreier ψ⁻¹ 1).obj.carrier)).symm ≪≫
      (sa)^*ᵃ[l].mapIso ((ObjectProperty.ι _ ⋙ Endofunctor.IsoAlgebra.forget _).mapIso E))
  exact ⟨B', i', p' ≫ e.hom, hB', hi', epi_comp _ _⟩


/-- The twisted dual `M^∨ ⊗ 𝓑_b` of an irreducible lisse sheaf `M` is irreducible lisse: the
dual is irreducible lisse (`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.dual`), and so are
its constant twists. (blueprint: `proposition-purity-lisse-part-fourier-transform`, part (2)) -/
theorem isIrreducibleLisse_twistedDual (D : LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse) (b : (PadicAlgCl l)ˣ) :
    (D.twistedDual b).sheaf.IsIrreducibleLisse :=
  IsIrreducibleLisse.constantTwist hD.dual b

/-- If the lisse sheaf `M` of `D` is nonexceptional for `ψ`, the twisted dual `M^∨ ⊗ 𝓑_b` is
nonexceptional for `ψ⁻¹`: the constant twist does not change the geometric constituents.
(blueprint: `proposition-purity-lisse-part-fourier-transform`, part (2)) -/
theorem isNonexceptional_twistedDual (D : LisseOnDenseOpen k₀ l)
    {ψ : AddChar k₀ (PadicAlgCl l)} (h : D.sheaf.IsNonexceptional ψ D.j) (b : (PadicAlgCl l)ˣ) :
    (D.twistedDual b).sheaf.IsNonexceptional ψ⁻¹ (D.twistedDual b).j :=
  (isNonexceptional_constantTwist { D with sheaf := D.sheaf.dual D.lisse, lisse := D.lisse.dual }
    b).2 (D.isNonexceptional_dual h)

end WeilSheaf.LisseOnDenseOpen

end AlgebraicGeometry
