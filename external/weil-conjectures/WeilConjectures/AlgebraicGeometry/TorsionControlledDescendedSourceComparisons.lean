/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import all WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.CompatibleQuotientFormalComparisons
import WeilConjectures.Topology.GlueSheavesOfModules
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Torsion-controlled local descent data

Source: Stacks Project, Tag 0889(1), Zariski locality by uniqueness;
Sheaves, Tags 00AL and 00AM.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- A descended source with compatible quotient maps yields the formal comparisons and arrow.
This lemma assumes that the source and its transition identifications are already glued.
It has no torsion or local-existence hypothesis and constructs no overlap comparisons.

Source: Stacks Project, Tag 0889(1), sheaf descent after the uniqueness argument;
Sheaves, Tags 00AL and 00AM.
(blueprint: new-stage3-torsion-controlled-descended-source-comparisons).

Proof: Compose each φi with li through overFunctorEquiv to identify M restricted to Ui
with Fi. Coherence is invariant under these isomorphisms and is local on the cover,
so M is coherent. The maps φi followed by bi agree on overlaps by hφ and hbcompat;
morphism descent gives a map a to H, and its restriction equation follows from hbi.
The maps φi followed by qi likewise agree by hφ and hqcompat. Their equations hqi
identify them with the canonical quotient maps of Fi followed by βi.inv. Exact
restriction and its compatibility with ideal powers and ideal-module products give
canonical normalized completion-restriction isomorphisms for M. Consequently the
local quotients induced by these maps are isomorphic to N at each level. Invert
these isomorphisms to obtain ε. They commute with transitions because βi and the
quotient projections do; their hom components agree on overlaps because the qi do
and quotient projections are epimorphisms. Finally hδ proves the local factorization
by precomposing with the quotient projection and cancelling that epimorphism.
For J=0 these are the original maps. For J=1 the quotient systems are zero.
For an empty cover X is empty, coherence and all equations are vacuous.
-/
theorem torsionControlled_descended_source_comparisons
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (ι : Type u) (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (Hlocal : ∀ i, CoherentModules (U i).toScheme)
    (hHlocal : ∀ i, (Hlocal i).obj = (Scheme.Modules.restrictFunctor (U i).ι).obj H.obj)
    (Fi : ∀ i, CoherentModules (U i).toScheme)
    (ai : ∀ i, Fi i ⟶ Hlocal i)
    (βi : ∀ i, N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
      formalCompletionSystem (J.comap (U i).ι) (Fi i).obj)
    (Li : ∀ i, SheafOfModules ((moduleRings X.toRingedSpace).over (U i)))
    (li : ∀ i, (Scheme.Modules.overEquiv (U i)).functor.obj (Li i) ≅ (Fi i).obj)
    (bi : ∀ i, Li i ⟶ H.obj.over (U i))
    (qi : ∀ (i : ι) (n : ℕᵒᵖ), Li i ⟶ (N.obj.obj n).over (U i))
    (θ : ∀ i j,
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE inf_le_left : U i ⊓ U j ⟶ U i)).obj (Li i) ≅
      (SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE inf_le_right : U i ⊓ U j ⟶ U j)).obj (Li j))
    (hbi : (∀ i, (Scheme.Modules.overEquiv (U i)).functor.map (bi i) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app H.obj ≫
          eqToHom (hHlocal i).symm = (li i).hom ≫ (ai i).hom))
    (hqi : (∀ (i : ι) (n : ℕᵒᵖ), (Scheme.Modules.overEquiv (U i)).functor.map (qi i n) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app (N.obj.obj n) =
          (li i).hom ≫ formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Fi i).obj ≫
            (βi i).inv.app n))
    (hδ : (∀ (i : ι) (n : ℕᵒᵖ), qi i n ≫ (δ.hom.app n).over (U i) =
        bi i ≫ (formalModuleQuotientπ J (n.unop + 1) H.obj).over (U i)))
    (hbcompat : (∀ (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (bi j).val.app (op (Over.mk (homOfLE hj))) =
            (bi i).val.app (op (Over.mk (homOfLE hi)))))
    (hqcompat : (∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) ≫
          (qi j n).val.app (op (Over.mk (homOfLE hj))) =
            (qi i n).val.app (op (Over.mk (homOfLE hi)))))
    (M : X.Modules) (φ : ∀ i, M.over (U i) ≅ Li i)
    (hφ : ∀ (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
      (φ i).hom.val.app (op (Over.mk (homOfLE hi))) ≫
        (θ i j).hom.val.app (op (Over.mk (homOfLE (le_inf hi hj)))) =
          (φ j).hom.val.app (op (Over.mk (homOfLE hj)))) :
    ∃ (hM : RingedSpace.IsCoherent X.toRingedSpace M),
    ∃ (a : (⟨M, hM⟩ : CoherentModules X) ⟶ H)
      (ε : ∀ i, N.obj ⋙ SheafOfModules.overFunctor
        (moduleRings X.toRingedSpace) (U i) ≅
        ((completion X J).obj ⟨M, hM⟩).obj ⋙ SheafOfModules.overFunctor
          (moduleRings X.toRingedSpace) (U i)),
      (∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
        ((ε i).hom.app n).val.app (op (Over.mk (homOfLE hi))) =
          ((ε j).hom.app n).val.app (op (Over.mk (homOfLE hj)))) ∧
      (∀ (n : ℕᵒᵖ) (i : ι), (δ.hom.app n).over (U i) =
        (ε i).hom.app n ≫ (((completion X J).map a).hom.app n).over (U i)) ∧
      (∀ i, ∃ e : (Scheme.Modules.restrictFunctor (U i).ι).obj M ≅ (Fi i).obj,
        (Scheme.Modules.restrictFunctor (U i).ι).map a.hom ≫
          eqToHom (hHlocal i).symm = e.hom ≫ (ai i).hom) := by
  classical
  let e (i : ι) : (Scheme.Modules.restrictFunctor (U i).ι).obj M ≅ (Fi i).obj :=
    ((Scheme.Modules.overFunctorEquiv (U i)).app M).symm ≪≫
      (Scheme.Modules.overEquiv (U i)).functor.mapIso (φ i) ≪≫ li i
  have hM : RingedSpace.IsCoherent X.toRingedSpace M :=
    (coherent_module_local_on_open_cover X M ι U hcover).2
      (fun i ↦ RingedSpace.coherent_iso (U i).toScheme.toRingedSpace (e i).symm (Fi i).property)
  have hb : ∀ (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
      ((φ i).hom ≫ bi i).val.app (op (Over.mk (homOfLE hi))) =
        ((φ j).hom ≫ bi j).val.app (op (Over.mk (homOfLE hj))) := by
    intro i j W hi hj
    change (φ i).hom.val.app (op (Over.mk (homOfLE hi))) ≫
      (bi i).val.app (op (Over.mk (homOfLE hi))) =
        (φ j).hom.val.app (op (Over.mk (homOfLE hj))) ≫
          (bi j).val.app (op (Over.mk (homOfLE hj)))
    rw [← hbcompat i j W hi hj, ← Category.assoc, hφ i j W hi hj]
  obtain ⟨b, hb, _⟩ :=
    (glue_sheaves_of_modules.{u, u} X.toRingedSpace ι U hcover).1 M H.obj
      (fun i ↦ (φ i).hom ≫ bi i) hb
  let F : CoherentModules X := ⟨M, hM⟩
  let a : F ⟶ H := ObjectProperty.homMk b
  let pi (i : ι) (n : ℕᵒᵖ) := (φ i).hom ≫ qi i n
  have hpi (i : ι) (n : ℕᵒᵖ) :
      (Scheme.Modules.overEquiv (U i)).functor.map (pi i n) ≫
        (Scheme.Modules.overFunctorEquiv (U i)).hom.app (N.obj.obj n) =
      (Scheme.Modules.overFunctorEquiv (U i)).hom.app F.obj ≫ (e i).hom ≫
        formalModuleQuotientπ (J.comap (U i).ι) (n.unop + 1) (Fi i).obj ≫
          (βi i).inv.app n := by
    simp only [pi, Functor.map_comp, Category.assoc, hqi]
    simp [e, F, Category.assoc]
  have hpcompat : ∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
      (pi i n).val.app (op (Over.mk (homOfLE hi))) =
        (pi j n).val.app (op (Over.mk (homOfLE hj))) := by
    intro n i j W hi hj
    change (φ i).hom.val.app (op (Over.mk (homOfLE hi))) ≫
      (qi i n).val.app (op (Over.mk (homOfLE hi))) =
        (φ j).hom.val.app (op (Over.mk (homOfLE hj))) ≫
          (qi j n).val.app (op (Over.mk (homOfLE hj)))
    rw [← hqcompat n i j W hi hj, ← Category.assoc, hφ i j W hi hj]
  have hpδ (i : ι) (n : ℕᵒᵖ) : pi i n ≫ (δ.hom.app n).over (U i) =
      a.hom.over (U i) ≫ (formalModuleQuotientπ J (n.unop + 1) H.obj).over (U i) := by
    change ((φ i).hom ≫ qi i n) ≫ _ = b.over (U i) ≫ _
    rw [hb i, Category.assoc, hδ i n, Category.assoc]
  obtain ⟨ε, hε, hδε⟩ := compatible_quotient_formal_comparisons
    J H F N δ a ι U Fi e βi pi hpi hpcompat hpδ
  refine ⟨hM, a, ε, hε, hδε, ?_⟩
  intro i
  refine ⟨e i, ?_⟩
  change (Scheme.Modules.restrictFunctor (U i).ι).map b ≫
    eqToHom (hHlocal i).symm = _
  have hn := (Scheme.Modules.overFunctorEquiv (U i)).hom.naturality b
  change (Scheme.Modules.overEquiv (U i)).functor.map (b.over (U i)) ≫
      (Scheme.Modules.overFunctorEquiv (U i)).hom.app H.obj =
    (Scheme.Modules.overFunctorEquiv (U i)).hom.app M ≫
      (Scheme.Modules.restrictFunctor (U i).ι).map b at hn
  apply (cancel_epi ((Scheme.Modules.overFunctorEquiv (U i)).hom.app M)).mp
  simp only [← Category.assoc, ← hn, hb, Functor.map_comp]
  simp [e, Category.assoc, hbi]


end AlgebraicGeometry
