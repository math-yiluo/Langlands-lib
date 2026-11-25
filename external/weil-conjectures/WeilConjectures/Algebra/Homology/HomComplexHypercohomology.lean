/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.RingedSiteZerothHypercohomology
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.CategoryTheory.Functor.Currying
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.HomComplexGlobalHomotopy
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Hypercohomology of a sheaf Hom complex with K-injective target

Source: Stacks Project, Tags 08JA, 0A95, and 0A96.
(blueprint: lem-pur-hom-complex-hypercohomology)
-/

@[expose] public section

universe u w
open CategoryTheory Opposite
namespace CategoryTheory

private theorem bijective_precomp_quotient
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {K L T : CochainComplex A ℤ} (t : K ⟶ L) [QuasiIso t] [T.IsKInjective] :
    Function.Bijective (fun f :
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj T ↦
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map t ≫ f) := by
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let a := DerivedCategory.Qh.map (q.map t)
  have ha : IsIso a := by
    change IsIso ((q ⋙ DerivedCategory.Qh).map t)
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) t).2 inferInstance
  have hK := CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) T
  have hL := CochainComplex.IsKInjective.Qh_map_bijective (q.obj L) T
  constructor
  · intro f g h
    apply hL.injective
    apply (cancel_epi a).mp
    change DerivedCategory.Qh.map (q.map t) ≫ _ = _
    simpa only [a, q, Functor.map_comp] using congrArg DerivedCategory.Qh.map h
  · intro g
    obtain ⟨f, hf⟩ := hL.surjective (inv a ≫ DerivedCategory.Qh.map g)
    refine ⟨f, hK.injective ?_⟩
    rw [Functor.map_comp, hf]
    exact IsIso.hom_inv_id_assoc a _

/-- Zeroth hypercohomology of the sheaf Hom complex into K-injectives computes
homotopy classes, naturally in the source and in any functorial K-injective target.

Source: Stacks Project, Lemma 08JA, using Lemmas 0A95 and 0A96.
(blueprint: lem-pur-hom-complex-hypercohomology)

Proof: first suppose the source L is K-flat. The sheaf Hom complex Hom(L,I(M))
is K-injective by Lemma 0A96. The comparison for the right derived global sections
functor therefore computes its hypercohomology by applying Hom(O,-) termwise.
The global-cochain comparison identifies this complex with the ordinary Hom
complex of L and I(M), compatibly with differentials. Its degree-zero cycles
are chain maps and its boundaries are null-homotopic maps; Mathlib's Hom-complex
cohomology comparison identifies H0 with morphisms in the homotopy category.
For arbitrary L choose a K-flat resolution K -> L (Lemma 06YS). Lemma 0A95
makes Hom(L,I(M)) -> Hom(K,I(M)) a quasi-isomorphism. Precomposition by K -> L
also gives a bijection of homotopy classes into I(M), by K-injectivity. Transport
the preceding comparison across these two isomorphisms. Choose the K-flat
augmentations degreewise surjective, as in Lemma 06YS.
For two such resolutions of L their fibre product maps quasi-isomorphically
to both: its projection kernels are the acyclic kernels of the augmentations.
Resolve that fibre product again by Lemma 06YS. Naturality of the K-flat
comparison for the resulting maps proves independence of the resolution.
For a source map L' -> L, pull back a surjective resolution of L to L' and
resolve that pullback. Its map to L' is a quasi-isomorphism, and its map to the
resolution of L yields the naturality square between K-flat sources. Transport
this square back to L and L'. The product-projection map formula makes the
global-cochain comparison commute with pre- and postcomposition; quotienting
by homotopy does too. Postcomposition by I(f) also commutes with the transport.
This proves naturality in both variables. All maps are additive. Products in
the Hom complex allow unbounded L.
For L=0 or I(M)=0 both sides are zero, so no nonzero or boundedness hypothesis
is needed. This theorem computes a complex-level Hom object, and does not use
derived internal Hom or the desired derived-category identification. -/
theorem homComplex_hypercohomology
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    (I : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hI : ∀ M, (I.obj M).IsKInjective) :
    Nonempty (((𝟭 _).prod I ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)) ⋙
        DerivedCategory.Q ⋙ ringedSiteZerothHypercohomology J R) ≅
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).op).prod
          (I ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ)) ⋙
        Functor.uncurry.obj preadditiveCoyoneda) := by
  classical
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  let Γ : A ⥤ AddCommGrpCat.{u} := preadditiveCoyoneda.obj
    (op (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) 0
  let Hd := DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0
  let G := Γ.mapHomologicalComplex (ComplexShape.up ℤ)
  let e : q ⋙ Γ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ≅
      G ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (Γ.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft G (DerivedCategory.quotientCompQhIso AddCommGrpCat.{u})
  let α : G ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor :=
    e.inv ≫ Functor.whiskerLeft q Γ.rightDerivedFunctorUnit ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
        Γ.rightDerivedFunctor).hom
  let β : G ⋙ H ⟶ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor ⋙ Hd :=
    (Functor.isoWhiskerLeft G
      (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0)).inv ≫
        Functor.whiskerRight α Hd
  have hβ (T : CochainComplex A ℤ) [T.IsKInjective] : IsIso (β.app T) := by
    dsimp [β, α]
    infer_instance
  let P := (𝟭 (CochainComplex A ℤ)ᵒᵖ).prod I
  let F := P ⋙ Functor.uncurry.obj (homComplexFunctor (R := R))
  let γ := Functor.whiskerLeft F β
  obtain ⟨c⟩ := homComplex_global_homotopy J R
  let c' := Functor.associator P (Functor.uncurry.obj (homComplexFunctor (R := R)))
    (G ⋙ H) ≪≫ Functor.isoWhiskerLeft P c
  have hγ : ∀ X, IsIso (γ.app X) := by
    rintro ⟨L, M⟩
    obtain ⟨K, t, hK, _, ht, _⟩ := CochainComplex.exists_isKFlatResolution L.unop
    let := ht
    let := hI M
    let f : (L, M) ⟶ (op K, M) := (t.op, 𝟙 M)
    have hflat : (homComplex (R := R) K (I.obj M)).IsKInjective :=
      CochainComplex.isKInjective_homComplex_of_isKFlat K (I.obj M) hK
    have hright : IsIso ((F ⋙ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor ⋙ Hd).map f) := by
      have hf : QuasiIso (F.map f) := by
        change QuasiIso (((homComplexFunctor (R := R)).map t.op).app (I.obj M) ≫
          ((homComplexFunctor (R := R)).obj (op K)).map (I.map (𝟙 M)))
        rw [I.map_id]
        exact quasiIso_homComplex_map (𝟙 (I.obj M)) t
      let := hf
      change IsIso (Hd.map (Γ.rightDerivedFunctor.map (DerivedCategory.Q.map (F.map f))))
      infer_instance
    have hleft : IsIso ((F ⋙ G ⋙ H).map f) := by
      apply (NatIso.isIso_map_iff c' f).mpr
      rw [ConcreteCategory.isIso_iff_bijective]
      change Function.Bijective (fun g ↦ (q.map t ≫ g) ≫ q.map (I.map (𝟙 M)))
      simpa only [I.map_id, q.map_id, Category.comp_id] using
        bijective_precomp_quotient (T := I.obj M) t
    let := hleft
    let := hright
    dsimp only [homComplex] at hflat
    let := hflat
    have : IsIso (γ.app (op K, M)) := by
      dsimp only [γ, Functor.whiskerLeft_app, F, P, Functor.comp_obj,
        Functor.prod_obj, Functor.id_obj, Functor.uncurry_obj_obj]
      exact hβ _
    have hn := γ.naturality f
    have : IsIso (γ.app (L, M) ≫
        (F ⋙ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor ⋙ Hd).map f) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right (γ.app (L, M))
      ((F ⋙ DerivedCategory.Q ⋙ Γ.rightDerivedFunctor ⋙ Hd).map f)
  let : IsIso γ := (NatTrans.isIso_iff_isIso_app γ).mpr hγ
  exact ⟨(asIso γ).symm ≪≫ c'⟩

end CategoryTheory
