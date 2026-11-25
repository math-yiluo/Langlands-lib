/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.BoundedAboveFlatTensorAcyclic
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

/-!
# Bounded-above flat complexes on a ringed site are K-flat

Source: Stacks Project, Cohomology on Sites, Lemma 21.17.8 (Tag 06YQ), also used in the
proof of Lemma 06YS (blueprint: lem-pc-bounded-above-flat-kflat-site).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private lemma acyclic_of_isColimit
    {D I : Type*} [Category* D] [Abelian D] [Category* I]
    [HasColimitsOfShape I D] [HasExactColimitsOfShape I D]
    (F : I ⥤ CochainComplex D ℤ) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (F.obj j).Acyclic) : c.pt.Acyclic := by
  intro i
  let S : ShortComplex (I ⥤ D) :=
    (ShortComplex.functorEquivalence I D).inverse.obj
      (F ⋙ HomologicalComplex.shortComplexFunctor D (.up ℤ) i)
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
    intro j
    exact IsZero.of_iso ((hF j i).isZero_homology)
      (S.mapHomologyIso ((evaluation I D).obj j)).symm
  have hc₁ := isColimitOfPreserves
    (HomologicalComplex.eval D (.up ℤ) ((ComplexShape.up ℤ).prev i)) hc
  have hc₂ := isColimitOfPreserves (HomologicalComplex.eval D (.up ℤ) i) hc
  have hc₃ := isColimitOfPreserves
    (HomologicalComplex.eval D (.up ℤ) ((ComplexShape.up ℤ).next i)) hc
  exact colim.exact_mapShortComplex hS hc₁ hc₂ hc₃
    (c.pt.d _ i) (c.pt.d i _)
    (fun j ↦ (c.ι.app j).comm _ _) (fun j ↦ (c.ι.app j).comm _ _)

/-- (blueprint: lem-pc-bounded-above-flat-kflat-site) A bounded-above cochain complex of
flat sheaves of modules over a sheaf of commutative rings on a site is K-flat.
Source: Stacks Project, Cohomology on Sites, Lemma 21.17.8 (Tag 06YQ), used in Tag 06YS.

Proof:
1. Given an acyclic complex `A`, its good truncations `τ≤m A` are acyclic and bounded above:
   the cohomology agrees with that of `A` below and at `m`, and vanishes above `m`
   (`def-pc-acyclic-complex-modules`). Their filtered termwise colimit is `A`.
   Tensor products and totalization commute with these colimits
   (`lem-pc-module-filtered-colimits-tensor`, `def-pc-tensor-complex-sheaves`). Exactness of
   filtered colimits implies that a filtered colimit of acyclic complexes is acyclic.
2. For each bounded-above acyclic truncation, its total tensor complex with `P` is acyclic
   by `lem-pc-bounded-above-flat-tensor-acyclic`, since every term of `P` is flat
   (`def-pc-flat-sheaf-modules`). Thus the total tensor complex with the original `A` is acyclic.
3. Since `A` was arbitrary, `def-pc-kflat-complex` gives K-flatness of `P`. -/
theorem isKFlat_of_boundedAbove_flat
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {R : Sheaf J CommRingCat.{u}}
    (P : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i)) : P.IsKFlatTensor := by
  let := SheafOfModules.monoidalCategory R
  intro A hA
  let M := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  -- Lift the integer indexing category to the universe of the colimit theorem.
  let I := AsSmall.{u} ℤ
  let down : I ⥤ ℤ := AsSmall.down
  have : down.IsEquivalence := inferInstanceAs ((AsSmall.equiv (C := ℤ)).inverse.IsEquivalence)
  let T : CochainComplex M ℤ ⥤ CochainComplex M ℤ :=
    (((MonoidalCategory.curriedTensor M).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).flip.obj P) ⋙
      HomologicalComplex₂.totalFunctor M (.up ℤ) (.up ℤ) (.up ℤ)
  have hcol := SheafOfModules.filteredColimitsTensorComplex C J R I
  have : HasExactColimitsOfShape I M := hcol.1
  have : PreservesColimitsOfShape I T := hcol.2 P
  let c := A.filtrationLECocone.whisker down
  have hc : IsColimit c :=
    (Functor.Final.isColimitWhiskerEquiv down A.filtrationLECocone).symm
      A.isColimitFiltrationLECocone
  change (T.obj A).Acyclic
  apply acyclic_of_isColimit _ (T.mapCocone c) (isColimitOfPreserves T hc)
  intro j
  have hb : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero ((A.truncLE (down.obj j : ℤ)).X i) := by
    refine ⟨down.obj j, fun i hi ↦ ?_⟩
    exact (A.truncLE (down.obj j : ℤ)).isZero_of_isStrictlyLE _ i hi
  have ha : (A.truncLE (down.obj j : ℤ)).Acyclic := by
    apply (A.acyclic_truncLE_iff _ ((down.obj j : ℤ) + 1)).2
    exact (A.isGE_iff _).2 (fun i _ ↦ hA i)
  exact acyclic_mapBifunctor_of_boundedAbove_flat_sheaf _ P hb hbounded hflat ha

end CochainComplex
