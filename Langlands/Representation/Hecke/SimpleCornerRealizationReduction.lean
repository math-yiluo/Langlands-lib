import Langlands.Representation.Hecke.FixedVectorCornerStatements
import Langlands.Representation.Hecke.NondegenerateModuleEquivalenceStatement
import Langlands.Representation.Hecke.LocalUnitsProof
import Langlands.Algebra.NonUnitalModuleCornerSimpleStatements
import Langlands.Representation.Category.Abelian
import Langlands.Representation.Category.Subquotients
import Langlands.Topology.LocallyProfiniteProof

/-! # Comparison with the abstract idempotent corner for realization -/

noncomputable section

namespace Langlands.Hecke

open CategoryTheory MeasureTheory

universe u v

section Corner

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

private def compactOpenIdempotent : Algebra.Idempotent (HeckeAlgebra μ) :=
  ⟨HeckeAlgebra.normalizedIndicator μ K hK,
    HeckeAlgebra.normalizedIndicator_idempotent μ K hK⟩

private def abstractCornerEquiv :
    Algebra.Idempotent.Corner (compactOpenIdempotent μ K hK) ≃+*
      HeckeAlgebra.Corner μ K hK where
  toFun f := ⟨f.val, (HeckeAlgebra.mem_biInvariant_iff_sandwich μ K hK f.val).mpr f.property⟩
  invFun f := ⟨f.val, (HeckeAlgebra.mem_biInvariant_iff_sandwich μ K hK f.val).mp f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

end Corner

private theorem heckeIdempotented
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] :
    Algebra.IsIdempotented (HeckeAlgebra μ) := by
  intro s
  obtain ⟨K, hK, _, he, hunit⟩ :=
    HeckeAlgebra.finiteFamilyLocalUnits G μ s (⊤ : OpenSubgroup G)
  refine ⟨⟨HeckeAlgebra.normalizedIndicator μ K hK, he⟩, ?_⟩
  intro f hf
  change HeckeAlgebra.normalizedIndicator μ K hK * f *
    HeckeAlgebra.normalizedIndicator μ K hK = f
  rw [(hunit f hf).1, (hunit f hf).2]

private theorem irreducible_of_categorical_simple
    {G : Type u} [Group G] [TopologicalSpace G]
    (A : SmoothRep.{0, u, v} ℂ G) [Simple A] : A.IsIrreducible := by
  classical
  have hnA : ¬ Subsingleton A := by
    intro hs
    apply id_nonzero A
    ext x
    exact hs.elim _ _
  let _ : Nontrivial A := not_subsingleton_iff_nontrivial.mp hnA
  have hsub : Nontrivial (Subrepresentation A.representation) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro heq
    exact (bot_ne_top : (⊥ : Submodule ℂ A) ≠ ⊤)
      (congrArg Subrepresentation.toSubmodule heq)
  let _ := hsub
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  let i := SmoothRep.subtype A S
  let _ : Mono i := (SmoothRep.mono_iff_injective i).mpr
    (SmoothRep.subtype_injective A S)
  have hi : i ≠ 0 := by
    intro hi
    apply hS
    apply Subrepresentation.ext
    apply eq_bot_iff.mpr
    intro x hx
    have hx0 := congrArg
      (fun f : SmoothRep.subrepresentation A S ⟶ A => SmoothRep.hom f ⟨x, hx⟩) hi
    exact (Submodule.mem_bot ℂ).mpr hx0
  let _ : IsIso i := isIso_of_mono_of_nonzero hi
  let e := SmoothRep.equivOfIso (asIso i)
  apply top_unique
  intro x _
  obtain ⟨y, hy⟩ := e.toLinearEquiv.surjective x
  rcases y with ⟨y, hyS⟩
  change y = x at hy
  exact hy ▸ hyS

open Algebra.NonUnitalModuleCorner Algebra.NonUnitalModuleCornerInduction

attribute [local instance] rightCornerModule
  Algebra.NonUnitalModuleCornerInduction.cornerModule tensorModule

/-- The realization assertion reduced to the existing general I.3.2 and III.1.4 targets. -/
theorem simpleCornerRealization_of_general_theorems
    (hind : Algebra.NonUnitalModuleCornerSimpleStatements.SimpleInducedQuotientStatement.{u, v})
    (hfixed : Algebra.NonUnitalModuleCornerSimpleStatements.FixedPartInducedQuotientStatement.{u, v})
    (hrep : HeckeNondegenerateModuleEquivalenceStatement.{u, max u v}) :
    SimpleCornerModuleRealizationStatement.{u, v} := by
  classical
  intro G _ _ _ _ _ _ _ _ μ _ K hK W _ _ hW
  let _ : NonarchimedeanGroup G := {
    is_nonarchimedean := fun U hU => by
      obtain ⟨J, _, hJU⟩ := (Topology.LocallyProfiniteProof.vanDantzig G).mp
        Topology.isLocallyProfinite_of_mathlib |>.2 U hU
      exact ⟨J, hJU⟩ }
  let e := compactOpenIdempotent μ K hK
  let E := abstractCornerEquiv μ K hK
  let _ : Module (Algebra.Idempotent.Corner e) W := Module.compHom W E.toRingHom
  have hW' : IsSimpleModule (Algebra.Idempotent.Corner e) W := by
    rw [isSimpleModule_iff_toSpanSingleton_surjective] at hW ⊢
    refine ⟨hW.1, fun w hw z => ?_⟩
    obtain ⟨a, ha⟩ := hW.2 w hw z
    refine ⟨E.symm a, ?_⟩
    change E (E.symm a) • w = z
    simpa only [E.apply_symm_apply, LinearMap.toSpanSingleton_apply] using ha
  let hH := heckeIdempotented μ
  let N := (Algebra.NonUnitalModuleCat.nondegenerateAnnihilatorQuotientFunctor e).obj
    (nondegenerateObject hH e W)
  have hN : Simple N := (hind (HeckeAlgebra μ) hH e W hW').1
  let _ := hN
  let F := heckeNondegenerateModuleFunctor.{u, max u v} μ
  let _ : F.IsEquivalence := hrep G μ
  let A := F.objPreimage N
  let i : F.obj A ≅ N := F.objObjPreimageIso N
  have hFA : Simple (F.obj A) := Simple.of_iso i
  let _ := hFA
  have hAsimple : Simple A := (simple_obj_iff F A).mp hFA
  let _ := hAsimple
  refine ⟨A, irreducible_of_categorical_simple A, ?_⟩
  let _ := Langlands.Hecke.cornerModule μ A.representation A.isSmooth K hK
  let _ := tensorAddCommGroup e W
  obtain ⟨J, _⟩ := hfixed (HeckeAlgebra μ) e W
  let J' : W ≃ₗ[Algebra.Idempotent.Corner e] FixedPart e N.obj := J
  let q : FixedPart e (F.obj A).obj ≃ₗ[Algebra.Idempotent.Corner e]
      FixedPart e N.obj :=
    ((Algebra.NonUnitalModuleCorner.nondegenerateFunctor e).mapIso i).toLinearEquiv
  let p : fixedVectors A.representation K.toSubgroup ≃+ FixedPart e (F.obj A).obj := {
    toFun := fun x => ⟨x.val, heckeAction_normalizedIndicator_of_fixed
      μ A.representation A.isSmooth K hK x.property⟩
    invFun := fun x => ⟨x.val, by
      have hx : heckeAction μ A.representation A.isSmooth
          (HeckeAlgebra.normalizedIndicator μ K hK) x.val = x.val := x.property
      rw [← hx]
      exact heckeAction_normalizedIndicator_mem μ A.representation A.isSmooth K hK x.val⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl }
  let r := p.trans (q.toAddEquiv.trans J'.symm.toAddEquiv)
  refine ⟨{ toAddEquiv := r, map_smul' := ?_ }⟩
  intro a x
  have hp : p (a • x) = E.symm a • p x := by
    apply Subtype.ext
    rfl
  change J'.symm (q (p (a • x))) = a • J'.symm (q (p x))
  rw [hp, q.map_smul, J'.symm.map_smul]
  change E (E.symm a) • J'.symm (q (p x)) = a • J'.symm (q (p x))
  rw [E.apply_symm_apply]

end Langlands.Hecke
