/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.AlgebraicGeometry.PerfectAffineMapRepresentative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # An affine chain representative of a bottom arrow

Source: Stacks Project, Tags 0BDL and 08CR, second proof.
(blueprint: lem-sc-zero-bottom-arrow-affine-chain-model). -/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme


private theorem exact_restriction_derived_iso {X Y : Scheme.{u}} (g : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (R : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (η : Scheme.Modules.tensorPullback g ≅ R) :
    Nonempty (derivedPullback g ≅ R.mapDerivedCategory) := by
  set_option backward.isDefEq.respectTransparency.types false in
    classical
    obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
      F, hF, hFmap, hFadd, ε, hL, htri, hK⟩ :=
      derivedPullback_spec g
    have h : F = Scheme.Modules.tensorPullback g :=
      CategoryTheory.Functor.ext hF (fun M N a ↦ hFmap a)
    subst F
    let P : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings X.toRingedSpace) := Scheme.Modules.tensorPullback g
    have : PreservesFiniteLimits P :=
      preservesFiniteLimits_of_natIso η.symm
    have : PreservesFiniteColimits P :=
      preservesFiniteColimits_of_natIso η.symm
    let W := HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)
    have : (derivedPullback g).IsLeftDerivedFunctor ε W := hL
    have : P.mapDerivedCategory.IsLeftDerivedFunctor
        P.mapDerivedCategoryFactorsh.hom W :=
      Functor.isLeftDerivedFunctor_of_inverts W _
        P.mapDerivedCategoryFactorsh
    exact ⟨Functor.leftDerivedUnique
      P.mapDerivedCategory (derivedPullback g)
      ε P.mapDerivedCategoryFactorsh.hom W ≪≫
        Functor.mapDerivedCategoryNatIso η⟩

private theorem scheme_affine_representative
    (X : Scheme.{u}) (W : X.Opens) (hW : IsAffineOpen W)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    (A B : CochainComplex
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) ℤ)
    (hA : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (A.X i))
    (hB : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (B.X i))
    (hAf : ∀ i : ℤ, ∃ n : ℕ, Nonempty (A.X i ≅ SheafOfModules.free
      (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (hBf : ∀ i : ℤ, ∃ n : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
      (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (f : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B) :
    ∃ α : A ⟶ B, DerivedCategory.Q.map α = f := by
  set_option backward.isDefEq.respectTransparency.types false in
    classical
    let C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W)
    let D := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)
    let : HasDerivedCategory C := HasDerivedCategory.standard C
    let E : C ≌ D := Modules.overEquiv W
    let F : C ⥤ D := E.functor
    let G : D ⥤ C := E.inverse
    have : F.Additive := Functor.additive_of_preserves_binary_products _
    have : G.Additive := Functor.additive_of_preserves_binary_products _
    let FC := F.mapHomologicalComplex (.up ℤ)
    let GC := G.mapHomologicalComplex (.up ℤ)
    let A' := GC.obj A
    let B' := GC.obj B
    let eunit : SheafOfModules.unit ((moduleRings X.toRingedSpace).over W) ≅
        G.obj (SheafOfModules.unit (moduleRings W.toScheme.toRingedSpace)) :=
      E.unitIso.app _ ≪≫ G.mapIso (Modules.overEquivFunctorObjUnitIso W).symm
    have hstrict (P : CochainComplex D ℤ)
        (hb : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (P.X i))
        (hf : ∀ i : ℤ, ∃ n : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
          (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n)))) :
        IsStrictlyPerfect X W (GC.obj P) := by
      obtain ⟨a, b, hb⟩ := hb
      refine ⟨⟨a, b, fun i hi ↦ G.map_isZero (hb i hi)⟩, ?_⟩
      intro i
      obtain ⟨n, ⟨e⟩⟩ := hf i
      let e' := G.mapIso e ≪≫ (SheafOfModules.mapFreeIso G (ULift.{u} (Fin n)) eunit).symm
      exact ⟨n, e'.hom, e'.inv, e'.hom_inv_id⟩
    let cA : FC.obj A' ≅ A := (NatIso.mapHomologicalComplex E.counitIso (.up ℤ)).app A
    let cB : FC.obj B' ≅ B := (NatIso.mapHomologicalComplex E.counitIso (.up ℤ)).app B
    let eA : F.mapDerivedCategory.obj (DerivedCategory.Q.obj A') ≅ DerivedCategory.Q.obj A :=
      F.mapDerivedCategoryFactors.app A' ≪≫ DerivedCategory.Q.mapIso cA
    let eB : F.mapDerivedCategory.obj (DerivedCategory.Q.obj B') ≅ DerivedCategory.Q.obj B :=
      F.mapDerivedCategoryFactors.app B' ≪≫ DerivedCategory.Q.mapIso cB
    have : F.mapDerivedCategory.Full := inferInstance
    let f' : DerivedCategory.Q.obj A' ⟶ DerivedCategory.Q.obj B' :=
      F.mapDerivedCategory.preimage (eA.hom ≫ f ≫ eB.inv)
    obtain ⟨α', hα'⟩ := perfect_affine_map_representative X W hW A' B'
      (hstrict A hA hAf) (hstrict B hB hBf) f'
    refine ⟨cA.inv ≫ FC.map α' ≫ cB.hom, ?_⟩
    have hnat := F.mapDerivedCategoryFactors.hom.naturality α'
    change F.mapDerivedCategory.map (DerivedCategory.Q.map α') ≫
        F.mapDerivedCategoryFactors.hom.app B' =
      F.mapDerivedCategoryFactors.hom.app A' ≫ DerivedCategory.Q.map (FC.map α') at hnat
    have hmap : DerivedCategory.Q.map (FC.map α') =
        F.mapDerivedCategoryFactors.inv.app A' ≫ F.mapDerivedCategory.map f' ≫
          F.mapDerivedCategoryFactors.hom.app B' := by
      rw [← hα']
      rw [hnat]
      simp
    have hf' : F.mapDerivedCategory.map f' = eA.hom ≫ f ≫ eB.inv :=
      F.mapDerivedCategory.map_preimage _
    simp only [Functor.map_comp, hmap, hf', eA, eB, Iso.trans_hom, Iso.trans_inv,
      Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
    simp


/-- A specified bottom arrow has a finite-free chain representative on an affine
refinement of a given zero-bottom chart. Its homology map in the bottom degree
is invertible; invertibility of its component is not part of this assertion.

Source: Stacks Project, Tag 0BDL, zero-matrix chart; Tag 08CR, second proof,
and Tag 0D5S, composition of derived pullbacks.
(blueprint: lem-sc-zero-bottom-arrow-affine-chain-model).

Proof: Choose an affine neighbourhood W of x inside U. Restrict K termwise to W,
obtaining B; exact restriction preserves its zero terms and zero differential,
and preserves finite free terms and the upper bound. Derived composition and
the exact restriction comparison give eB. Exact open pullback commutes naturally
with homology and with single complexes. The hypothesis hf therefore makes the
restricted arrow invertible on H^a. Since both bottom differentials of B vanish,
H^a(B) is B.X a. Identify the restriction of M with B.X a using this isomorphism,
and let A be the single complex on this finite free sheaf in degree a. It is
bounded above by a, finite free in all degrees (rank zero off a), and has all
other terms zero. The single-functor restriction comparison and this sheaf
isomorphism give eA. Transport A and B to the localized site over W via
Scheme.Modules.overEquiv W. Both are strictly perfect there. Apply the affine
perfect-map representative theorem to eA.inv followed by the restricted f
and eB.hom, and transport the resulting chain map back to W.toScheme.
Naturality of localization gives the displayed square. Apply H^a to that square;
the endpoint comparisons are isomorphisms and the restricted H^a(f) is invertible.
The homology factorization of Q then makes H^a(alpha) invertible. Rank zero,
a negative degree and an empty scheme do not alter the construction. -/
theorem zeroBottomArrow_affine_chain_model
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T : Scheme.{u}) (D : schemeDerivedCategory T) (a : ℤ)
    (M : SheafOfModules.{u} (moduleRings T.toRingedSpace))
    (f : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj M ⟶ D)
    (hf : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).map f))
    (U : T.Opens)
    (K : CochainComplex
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ)
    (hbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (K.X i))
    (hnegative : ∀ i : ℤ, i < a → IsZero (K.X i))
    (hzero : K.d a (a + 1) = 0)
    (hfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
      (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin n))))
    (e : (derivedPullback U.ι).obj D ≅ DerivedCategory.Q.obj K)
    (x : T) (hx : x ∈ U) :
    ∃ W : T.Opens, x ∈ W ∧ W ≤ U ∧ IsAffineOpen W ∧
      ∃ A B : CochainComplex
          (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) ℤ,
        (∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (A.X i)) ∧
        (∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (B.X i)) ∧
        (∀ i : ℤ, ∃ n : ℕ, Nonempty (A.X i ≅ SheafOfModules.free
          (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n)))) ∧
        (∀ i : ℤ, ∃ n : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
          (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n)))) ∧
        (∀ i : ℤ, i ≠ a → IsZero (A.X i)) ∧
        (∀ i : ℤ, i < a → IsZero (B.X i)) ∧ B.d a (a + 1) = 0 ∧
        ∃ α : A ⟶ B, IsIso (HomologicalComplex.homologyMap α a) ∧
          ∃ (eA : (derivedPullback W.ι).obj ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj M) ≅
                DerivedCategory.Q.obj A)
            (eB : (derivedPullback W.ι).obj D ≅ DerivedCategory.Q.obj B),
            (derivedPullback W.ι).map f ≫ eB.hom =
              eA.hom ≫ DerivedCategory.Q.map α := by
  set_option backward.isDefEq.respectTransparency.types false in
    classical
    let := hf
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    let j := T.homOfLE hWU
    let C := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)
    let CU := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)
    let CT := SheafOfModules.{u} (moduleRings T.toRingedSpace)
    let R : CT ⥤ C := Modules.restrictFunctor W.ι
    let S : CU ⥤ C := Modules.restrictFunctor j
    let RU : CT ⥤ CU := Modules.restrictFunctor U.ι
    have : RU.Additive := ⟨by intros; rfl⟩
    have : R.Additive := ⟨by intros; rfl⟩
    have : S.Additive := ⟨by intros; rfl⟩
    have : PreservesFiniteLimits R :=
      inferInstanceAs (PreservesFiniteLimits (Modules.restrictFunctor W.ι))
    have : PreservesFiniteColimits R :=
      inferInstanceAs (PreservesFiniteColimits (Modules.restrictFunctor W.ι))
    have : PreservesFiniteLimits S :=
      inferInstanceAs (PreservesFiniteLimits (Modules.restrictFunctor j))
    have : PreservesFiniteColimits S :=
      inferInstanceAs (PreservesFiniteColimits (Modules.restrictFunctor j))
    have : PreservesFiniteLimits RU :=
      inferInstanceAs (PreservesFiniteLimits (Modules.restrictFunctor U.ι))
    have : PreservesFiniteColimits RU :=
      inferInstanceAs (PreservesFiniteColimits (Modules.restrictFunctor U.ι))
    let ηU : Modules.tensorPullback U.ι ≅ RU :=
      (Modules.nonempty_tensorPullbackAdjunction U.ι).some.leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction U.ι) ≪≫
          (Modules.restrictFunctorIsoPullback U.ι).symm
    let ηR : Modules.tensorPullback W.ι ≅ R :=
      (Modules.nonempty_tensorPullbackAdjunction W.ι).some.leftAdjointUniq
        (Modules.pullbackPushforwardAdjunction W.ι) ≪≫
          (Modules.restrictFunctorIsoPullback W.ι).symm
    obtain ⟨cR⟩ := exact_restriction_derived_iso W.ι R ηR
    obtain ⟨cU⟩ := exact_restriction_derived_iso U.ι RU ηU
    let B := (S.mapHomologicalComplex (.up ℤ)).obj K
    have hBbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (B.X i) := by
      obtain ⟨c, hc⟩ := hbounded
      exact ⟨c, fun i hi ↦ S.map_isZero (hc i hi)⟩
    have hBnegative : ∀ i : ℤ, i < a → IsZero (B.X i) :=
      fun i hi ↦ S.map_isZero (hnegative i hi)
    have hBzero : B.d a (a + 1) = 0 := by
      change S.map (K.d a (a + 1)) = 0
      rw [hzero, S.map_zero]
    have hBfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (B.X i ≅ SheafOfModules.free
        (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))) := by
      intro i
      obtain ⟨n, ⟨ei⟩⟩ := hfree i
      exact ⟨n, ⟨S.mapIso ei ≪≫ Modules.restrictFreeIso j (ULift.{u} (Fin n))⟩⟩
    have : PreservesFiniteLimits (RU ⋙ S) := comp_preservesFiniteLimits RU S
    have : PreservesFiniteColimits (RU ⋙ S) := comp_preservesFiniteColimits RU S
    let cRestrict : R ≅ RU ⋙ S :=
      Modules.restrictFunctorCongr (T.homOfLE_ι hWU).symm ≪≫
        Modules.restrictFunctorComp j U.ι
    let eRU : RU.mapDerivedCategory.obj D ≅ DerivedCategory.Q.obj K :=
      (cU.app D).symm ≪≫ e
    let eB : (derivedPullback W.ι).obj D ≅ DerivedCategory.Q.obj B :=
      cR.app D ≪≫ (Functor.mapDerivedCategoryNatIso cRestrict).app D ≪≫
        (Functor.mapDerivedCategoryCompIso RU S).symm.app D ≪≫
        S.mapDerivedCategory.mapIso eRU ≪≫ S.mapDerivedCategoryFactors.app K
    let H := DerivedCategory.homologyFunctor C a
    have hrestriction : IsIso (H.map ((derivedPullback W.ι).map f)) := by
      have : IsIso ((R.mapDerivedCategory ⋙ H).map f) :=
        (NatIso.isIso_map_iff (R.mapDerivedCategoryHomologyFunctorIso a) f).1
          (by dsimp; exact R.map_isIso _)
      exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight cR H) f).2 this
    have hfB : (B.sc a).f = 0 := by
      change B.d ((ComplexShape.up ℤ).prev a) a = 0
      rw [(ComplexShape.up ℤ).prev_eq' (show a - 1 + 1 = a by omega)]
      exact (hBnegative (a - 1) (by omega)).eq_of_src _ _
    have hgB : (B.sc a).g = 0 := by
      change B.d a ((ComplexShape.up ℤ).next a) = 0
      rw [(ComplexShape.up ℤ).next_eq' (show a + 1 = a + 1 by rfl)]
      exact hBzero
    let eM : R.obj M ≅ B.X a :=
      (R.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso CT a).app M)).symm ≪≫
      (R.mapDerivedCategoryHomologyFunctorIso a).app _ ≪≫
      (H.mapIso (cR.app _)).symm ≪≫
      asIso (H.map ((derivedPullback W.ι).map f)) ≪≫ H.mapIso eB ≪≫
      (DerivedCategory.homologyFunctorFactors C a).app B ≪≫
      (ShortComplex.HomologyData.ofZeros (B.sc a) hfB hgB).left.homologyIso
    let A := (HomologicalComplex.single C (.up ℤ) a).obj (B.X a)
    have hAzero : ∀ i : ℤ, i ≠ a → IsZero (A.X i) :=
      fun i hi ↦ HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
    have hAbounded : ∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (A.X i) :=
      ⟨a, fun i hi ↦ hAzero i (by omega)⟩
    have hAfree : ∀ i : ℤ, ∃ n : ℕ, Nonempty (A.X i ≅ SheafOfModules.free
        (R := moduleRings W.toScheme.toRingedSpace) (ULift.{u} (Fin n))) := by
      intro i
      by_cases hi : i = a
      · subst i
        obtain ⟨n, ⟨ei⟩⟩ := hBfree a
        exact ⟨n, ⟨HomologicalComplex.singleObjXSelf (.up ℤ) a (B.X a) ≪≫ ei⟩⟩
      · have hz : IsZero (SheafOfModules.free (R := moduleRings W.toScheme.toRingedSpace)
            (ULift.{u} (Fin 0))) := by
          apply (IsZero.iff_id_eq_zero _).2
          apply (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin 0))).hom_ext
          intro i
          exact Fin.elim0 i.as.down
        exact ⟨0, ⟨(hAzero i hi).iso hz⟩⟩
    let eA : (derivedPullback W.ι).obj ((DerivedCategory.singleFunctor CT a).obj M) ≅
        DerivedCategory.Q.obj A :=
      cR.app _ ≪≫ (R.mapDerivedCategorySingleFunctor a).app M ≪≫
        (DerivedCategory.singleFunctor C a).mapIso eM ≪≫
        (DerivedCategory.singleFunctorIsoCompQ C a).app (B.X a)
    let g := eA.inv ≫ (derivedPullback W.ι).map f ≫ eB.hom
    obtain ⟨b, hb⟩ := hBbounded
    obtain ⟨α, hα⟩ := scheme_affine_representative T W hW A B
      ⟨a, a, fun i hi ↦ hAzero i (by omega)⟩
      ⟨a, b, fun i hi ↦ hi.elim (hBnegative i) (hb i)⟩ hAfree hBfree g
    have hg : IsIso (H.map g) := by
      dsimp [g]
      simp only [Functor.map_comp]
      infer_instance
    have hHα : IsIso (HomologicalComplex.homologyMap α a) := by
      have : IsIso (H.map (DerivedCategory.Q.map α)) := by rw [hα]; exact hg
      exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C a) α).1 this
    refine ⟨W, hxW, hWU, hW, A, B, hAbounded, ⟨b, hb⟩, hAfree, hBfree,
      hAzero, hBnegative, hBzero, α, hHα, eA, eB, ?_⟩
    rw [hα]
    simp [g]


end AlgebraicGeometry.Scheme
