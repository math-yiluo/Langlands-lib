/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import WeilConjectures.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Equivalence

import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-!
# Small locally constant sheaves from lattice-class presentations

Source: Bhatt--Scholze, Proposition 6.8.4(6), passage from lattice pairs to classes.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

open CategoryTheory.Limits Scheme.ProEt

set_option backward.isDefEq.respectTransparency false

private theorem ulift_preservesSheafification
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) :
    J.PreservesSheafification uliftFunctor.{u + 2, u + 1} := by
  have : EssentiallySmall.{u + 2} C := essentiallySmallSelf.{u + 2} C
  have : J.WEqualsLocallyBijective (Type (u + 2)) :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J
  constructor
  intro P Q f hf
  have := hf.isLocallyInjective
  have := hf.isLocallySurjective
  let g := Functor.whiskerRight f uliftFunctor.{u + 2, u + 1}
  have : Presheaf.IsLocallyInjective J g := by
    constructor
    intro X x y h
    have hh' : f.app X x.down = f.app X y.down :=
      congrArg (fun t : ULift.{u + 2} (Q.obj X) ↦ t.down) h
    have hh := Presheaf.equalizerSieve_mem J f x.down y.down hh'
    apply J.superset_covering _ hh
    intro W g hg
    exact ULift.ext hg
  have : Presheaf.IsLocallySurjective J g := by
    constructor
    intro X x
    apply J.superset_covering _ (Presheaf.imageSieve_mem J f x.down)
    intro W g hg
    obtain ⟨y, hy⟩ := hg
    exact ⟨ULift.up y, ULift.ext hy⟩
  exact J.W_of_isLocallyBijective g
private instance sliceFrom_dense (X : Scheme.{u}) (W : X.ProEt) :
    (sliceEquiv X W).inverse.IsDenseSubsite
      (topology W.left) ((topology X).over W) :=
  sliceDense X W

private theorem latticeClass_sections_small {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
    (c : ∀ U : X.ProEt, IntegralLatticePair a L U → F.obj.obj (op U))
    (h : IsLatticeClassPresentation a L F c) (U : X.ProEt) :
    Small.{u + 1} (F.obj.obj (op U)) := by
  classical
  let p (x : F.obj.obj (op U)) : IntegralLatticePair a L U := (h.1 U x).choose
  have hp (x : F.obj.obj (op U)) : c U (p x) = x := (h.1 U x).choose_spec
  let embed (x : F.obj.obj (op U)) :
      ∀ T : (Over U)ᵒᵖ, Set ((L.over U).val.obj T) := (p x).image
  apply small_of_injective.{u + 1, u + 1, u + 2} (f := embed)
  intro x y he
  have he' : ∀ T : Over U, (p x).image (op ((Over.map (𝟙 U)).obj T)) =
      (p y).image (op T) := by
    intro T
    change (p x).image (op (Over.mk (T.hom ≫ 𝟙 U))) = (p y).image (op T)
    rw [Category.comp_id]
    exact congrFun he (op T)
  have he'' := (h.2.2 U U (𝟙 U) (p x) (p y)).2 he'
  change F.obj.map (𝟙 (op U)) (c U (p x)) = c U (p y) at he''
  rw [F.obj.map_id, types_id_apply, hp, hp] at he''
  exact he''

private theorem small_latticeClass_sheaf {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
    (c : ∀ U : X.ProEt, IntegralLatticePair a L U → F.obj.obj (op U))
    (h : IsLatticeClassPresentation a L F c) :
    ∃ F' : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)),
      ∃ e : ∀ U : X.ProEt, F.obj.obj (op U) ≃ F'.obj.obj (op U),
        ∀ (U V : X.ProEt) (f : V ⟶ U) (x : F.obj.obj (op U)),
          e V (F.obj.map f.op x) = F'.obj.map f.op (e U x) := by
  have : FunctorToTypes.Small.{u + 1} F.obj :=
    fun V ↦ latticeClass_sections_small a L F c h V.unop
  let P := FunctorToTypes.shrink.{u + 1} F.obj
  have hP : Presheaf.IsSheaf (Scheme.ProEt.topology X) P := by
    rw [isSheaf_iff_isSheaf_of_type]
    apply Presieve.isSheaf_of_nat_equiv
      (P₁ := F.obj) (fun {V} ↦ equivShrink (F.obj.obj (op V))) ?_
        ((isSheaf_iff_isSheaf_of_type _ _).mp F.property)
    intro V W f x
    change equivShrink _ (F.obj.map f.op x) =
      equivShrink _ (F.obj.map f.op ((equivShrink _).symm (equivShrink _ x)))
    rw [Equiv.symm_apply_apply]
  refine ⟨⟨P, hP⟩, fun U ↦ equivShrink _, ?_⟩
  intro U V f x
  change equivShrink _ (F.obj.map f.op x) =
    equivShrink _ (F.obj.map f.op ((equivShrink _).symm (equivShrink _ x)))
  rw [Equiv.symm_apply_apply]

private noncomputable def small_constant_slice {X : Scheme.{u}}
    (F : Sheaf (topology X) (Type (u + 2)))
    (F₀ : Sheaf (topology X) (Type (u + 1)))
    (e : ∀ U : X.ProEt, F.obj.obj (op U) ≃ F₀.obj.obj (op U))
    (he : ∀ (U V : X.ProEt) (f : V ⟶ U) (x : F.obj.obj (op U)),
      e V (F.obj.map f.op x) = F₀.obj.map f.op (e U x))
    (U : X.ProEt) (A : Type u)
    (k : (constantSheaf ((topology X).over U) (Type (u + 2))).obj
      (ULift.{u + 2} A) ≅ F.over U) :
    (F₀.over U) ≅ (constantSheaf ((topology X).over U) (Type (u + 1))).obj
      (ULift.{u + 1} A) := by
  let J := (topology X).over U
  have : J.PreservesSheafification uliftFunctor.{u + 2, u + 1} :=
    ulift_preservesSheafification J
  let e₀ : (sheafCompose J uliftFunctor.{u + 2, u + 1}).obj (F₀.over U) ≅ F.over U := by
    apply ObjectProperty.isoMk _
    refine NatIso.ofComponents (fun V ↦ (Equiv.ulift.trans (e V.unop.left).symm).toIso) ?_
    intro V W f
    ext x
    dsimp
    apply (e W.unop.left).injective
    change e W.unop.left ((e W.unop.left).symm
      (F₀.obj.map f.unop.left.op x.down)) =
      e W.unop.left (F.obj.map f.unop.left.op ((e V.unop.left).symm x.down))
    rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply]
  let ek : (sheafCompose J uliftFunctor.{u + 2, u + 1}).obj
      ((constantSheaf J (Type (u + 1))).obj (ULift.{u + 1} A)) ≅
      (constantSheaf J (Type (u + 2))).obj (ULift.{u + 2} A) :=
    (constantCommuteCompose J uliftFunctor.{u + 2, u + 1}).app _ ≪≫
      (constantSheaf J (Type (u + 2))).mapIso
        ((Equiv.ulift.trans (Equiv.ulift.trans Equiv.ulift.symm)).toIso)
  exact ((fullyFaithfulSheafCompose J fullyFaithfulULiftFunctor).preimageIso
    (ek ≪≫ k ≪≫ e₀.symm)).symm

private noncomputable def constant_slice_smallSite {X : Scheme.{u}}
    (F₀ : Sheaf (topology X) (Type (u + 1))) (U : X.ProEt) (A : Type (u + 1))
    (k : F₀.over U ≅ (constantSheaf ((topology X).over U) (Type (u + 1))).obj A) :
    (Scheme.proEtaleSetRestriction X U).obj F₀ ≅
      (constantSheaf (topology U.left) (Type (u + 1))).obj A := by
  let G := (sliceEquiv X U).inverse
  let T : U.left.ProEt := MorphismProperty.Over.mk ⊤ (𝟙 U.left) (inferInstance)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  have hGT : IsTerminal (G.obj T) := hT.isTerminalObj G
  exact ((Functor.IsDenseSubsite.sheafEquiv (topology U.left) ((topology X).over U) G
    (Type (u + 1))).inverse.mapIso k) ≪≫
    ((equivCommuteConstant' (topology U.left) (Type (u + 1))
      ((topology X).over U) G hT hGT).app A).symm

private theorem small_latticeClass_local_properties {X : Scheme.{u}}
    {R S : Sheaf (topology X) CommRingCat.{u + 1}} (a : R ⟶ S)
    (L : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hL : L.IsFiniteLocallyFree)
    (F : Sheaf (topology X) (Type (u + 2)))
    (c : ∀ U : X.ProEt, IntegralLatticePair a L U → F.obj.obj (op U))
    (hF : IsLatticeClassPresentation a L F c)
    (hcosets : ∀ (U : X.ProEt) (n : ℕ)
      (_e : L.over U ≅ SheafOfModules.free
        (R := ((sheafCompose (topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).over U)
        (ULift.{u + 1} (Fin n))),
      ∃ A : Type u, Nonempty A ∧ Nonempty
        ((constantSheaf ((topology X).over U) (Type (u + 2))).obj
          (ULift.{u + 2} A) ≅ F.over U)) :
    ∃ F₀ : Sheaf (topology X) (Type (u + 1)),
      Scheme.IsProEtaleLocallyConstant X F₀ ∧
      (∃ (I : Type (u + 1)) (U : I → X.ProEt),
        (topology X).CoversTop U ∧
          ∀ i : I, Nonempty (F₀.obj.obj (op (U i)))) ∧
      ∀ U : X.ProEt, Nonempty (F₀.obj.obj (op U)) →
        Nonempty (IntegralLatticePair a L U) := by
  classical
  obtain ⟨F₀, e, he⟩ := small_latticeClass_sheaf a L F c hF
  obtain ⟨q, hq, hf⟩ := hL.exists_localGeneratorsData
  have := hq
  have desc (i : q.I) : ∃ A : Type u, Nonempty A ∧ Nonempty
      (F₀.over (q.X i) ≅
        (constantSheaf ((topology X).over (q.X i)) (Type (u + 1))).obj
          (ULift.{u + 1} A)) := by
    have := hf.isFiniteType i
    let := Fintype.ofFinite (q.generators i).I
    let n := Fintype.card (q.generators i).I
    let t : L.over (q.X i) ≅ SheafOfModules.free (ULift.{u + 1} (Fin n)) :=
      (asIso (q.generators i).π).symm ≪≫ SheafOfModules.freeFunctor.mapIso
        ((Fintype.equivFin (q.generators i).I).trans Equiv.ulift.symm).toIso
    obtain ⟨A, hA, ⟨k⟩⟩ := hcosets (q.X i) n t
    exact ⟨A, hA, ⟨small_constant_slice F F₀ e he (q.X i) A k⟩⟩
  refine ⟨F₀, ⟨q.I, q.X, q.coversTop, ?_⟩,
    ⟨q.I, q.X, q.coversTop, ?_⟩, ?_⟩
  · intro i
    obtain ⟨A, hA, ⟨k⟩⟩ := desc i
    exact ⟨ULift.{u + 1} A, ⟨constant_slice_smallSite F₀ (q.X i) _ k⟩⟩
  · intro i
    obtain ⟨A, ⟨a⟩, ⟨k⟩⟩ := desc i
    let V : Over (q.X i) := Over.mk (𝟙 (q.X i))
    exact ⟨k.inv.hom.app (op V)
      ((toSheafify ((topology X).over (q.X i))
        ((Functor.const _).obj (ULift.{u + 1} A))).app (op V) (ULift.up a))⟩
  · intro U ⟨x⟩
    exact ⟨(hF.1 U ((e U).symm x)).choose⟩

/-- A large lattice-class presentation, locally a nonempty constant coset sheaf,
gives a small locally constant, locally inhabited sheaf with lattice representatives,
after an isomorphism of its coefficient rings.
Source: Bhatt--Scholze, Proposition 6.8.4(6), lattice-class sheaf construction.
(auxiliary; not a blueprint node)

Proof: choose class representatives only inside this proof, and send each class to
its family of embedded integral submodules on every object of its slice. The exact
restriction criterion at the identity implies injectivity. Thus every section set
is small in universe u+1. Shrink these sets and transport restrictions and the sheaf
condition through the natural equivalences. The universe-lift functor preserves local
injectivity and local surjectivity; the locally bijective characterization of
sheafification therefore shows that it commutes with constant sheaves. Hence the
given constant-coset isomorphisms descend to the smaller section universe.
Choose finite local free generators for L' and identify each finite basis with Fin n.
These trivializations supply a cover with nonempty constant descriptions on its
slices. The canonical equivalence between a slice and the member's small pro-etale
site transports constant sheaves, giving local constancy in the required sense.
A value in the constant set maps through the sheafification unit at the identity
object to give a section on each member. For any inhabited section set, the inverse
shrinking equivalence and surjectivity of the class presentation give a lattice pair
for a', L'. Transport that single pair along the commuting coefficient square using
`integral_lattice_pair_of_coefficient_iso`. Empty covers and rank zero require no
nonemptiness assumption on the scheme or the finite bases. -/
theorem small_lattice_sheaf_of_coset_presentation {X : Scheme.{u}}
    {R S R' S' : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (a' : R' ⟶ S') (eR : R' ≅ R) (eS : S' ≅ S)
    (hsquare : a' ≫ eS.hom = eR.hom ≫ a)
    (L : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (L' : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S'))
    (eL : L' ≅ (SheafOfModules.pushforward (F := 𝟭 X.ProEt)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map eS.hom)).obj L)
    (hL' : L'.IsFiniteLocallyFree)
    (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
    (c : ∀ U : X.ProEt, IntegralLatticePair a' L' U → F.obj.obj (op U))
    (hF : IsLatticeClassPresentation a' L' F c)
    (hcosets : ∀ (U : X.ProEt) (n : ℕ)
      (_e : L'.over U ≅ SheafOfModules.free
        (R := ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S').over U)
        (ULift.{u + 1} (Fin n))),
      ∃ A : Type u, Nonempty A ∧ Nonempty
        ((constantSheaf ((Scheme.ProEt.topology X).over U) (Type (u + 2))).obj
          (ULift.{u + 2} A) ≅ F.over U)) :
    ∃ F₀ : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)),
      Scheme.IsProEtaleLocallyConstant X F₀ ∧
      (∃ (I : Type (u + 1)) (U : I → X.ProEt),
        (Scheme.ProEt.topology X).CoversTop U ∧
          ∀ i : I, Nonempty (F₀.obj.obj (op (U i)))) ∧
      ∀ U : X.ProEt, Nonempty (F₀.obj.obj (op U)) →
        Nonempty (IntegralLatticePair a L U) := by
  obtain ⟨F₀, hconst, hlocal, hrepresent⟩ :=
    small_latticeClass_local_properties a' L' hL' F c hF hcosets
  refine ⟨F₀, hconst, hlocal, ?_⟩
  intro U hx
  obtain ⟨P⟩ := hrepresent U hx
  exact integral_lattice_pair_of_coefficient_iso a a' eR eS hsquare L L' eL U P

end AlgebraicGeometry.ProEtale
