/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.FinitePresentation
import WeilConjectures.Algebra.FiniteRelationCokernelColimit
import WeilConjectures.Algebra.FinitePresentationRestrictedHomColimit
import WeilConjectures.Algebra.FiniteTensorVanishingColimit

/-!
# Finitely presented modules over a directed ring colimit

Source: Stacks Project, Algebra, Lemma 10.127.6 (Tag 05N7), used in Limits,
Lemma 32.10.2 (Tag 01ZR), affine case
(blueprint: lem-pc-fp-module-map-descent-affine).
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace ModuleCat

private theorem exists_comparison
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    (ri : R →+* A) (rij : R →+* S) (rj : S →+* A)
    (hc : rj.comp rij = ri) (M : ModuleCat.{max u v} R) :
    ∃ e : (extendScalars ri).obj M ≅ (extendScalars rj).obj ((extendScalars rij).obj M),
      ∀ m : M, e.hom ((1 : A) ⊗ₜ[R, ri] m) =
        (1 : A) ⊗ₜ[S, rj] ((1 : S) ⊗ₜ[R, rij] m) := by
  subst ri
  exact ⟨(extendScalarsComp rij rj).app M,
    extendScalarsComp_hom_app_one_tmul rij rj M⟩

/-- Over a directed colimit of commutative rings, finitely presented modules,
maps between their fixed base changes, and equalities of maps descend to a stage.

For objects, choose a finite free presentation and descend its relation cokernel.
Construct the stage module as the lifted quotient by the relation-map range; its
finite presentation follows from finite generation of that range. For a map,
uncurry it by the scalar extension-restriction adjunction, lift the resulting map
into a stage tensor module, and curry it there. Mathlib's composition comparison
provides the two canonical isomorphisms and their pure-tensor equations, which
prove the commuting square. For equality, take finitely many generators, apply
eventual tensor vanishing to the differences of their images, and use linear
extensionality on their span. The elementwise ring-colimit criterion remains
needed in the three lower lemmas.
The module universes are explicitly chosen to contain the ring universe, so that
stage modules and their scalar extensions lie in the same module category.
Source: Stacks Project, Algebra, Lemma 10.127.6 (Tag 05N7)
(blueprint: lem-pc-fp-module-map-descent-affine). -/
theorem finitePresentation_descent_directedColimit
    {I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat) :
    (∀ (N : ModuleCat.{max u v} (colimit F : CommRingCat)),
      Module.FinitePresentation (colimit F : CommRingCat) N →
      ∃ (i : I) (M : ModuleCat.{max u v} (F.obj i)), Module.FinitePresentation (F.obj i) M ∧
        Nonempty ((extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj M ≅ N)) ∧
    (∀ (i : I) (M N : ModuleCat.{max u w} (F.obj i)),
      Module.FinitePresentation (F.obj i) M →
      Module.FinitePresentation (F.obj i) N →
      ∀ (f : (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj M ⟶
          (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).obj N),
        ∃ (j : I) (hij : i ≤ j),
          let rij := CommRingCat.Hom.hom (F.map (homOfLE hij))
          let rj := CommRingCat.Hom.hom (colimit.ι F j)
          let ri := CommRingCat.Hom.hom (colimit.ι F i)
          ∃ (g : (extendScalars rij).obj M ⟶ (extendScalars rij).obj N)
            (eM : (extendScalars ri).obj M ≅
              (extendScalars rj).obj ((extendScalars rij).obj M))
            (eN : (extendScalars ri).obj N ≅
              (extendScalars rj).obj ((extendScalars rij).obj N)),
            (∀ m : M,
              eM.hom ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] m) =
                (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj]
                  ((1 : ↑(F.obj j)) ⊗ₜ[F.obj i, rij] m)) ∧
            (∀ n : N,
              eN.hom ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] n) =
                (1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj j, rj]
                  ((1 : ↑(F.obj j)) ⊗ₜ[F.obj i, rij] n)) ∧
            f ≫ eN.hom = eM.hom ≫ (extendScalars rj).map g) ∧
    (∀ (i : I) (M N : ModuleCat.{max u z} (F.obj i)),
      Module.FinitePresentation (F.obj i) M →
      Module.FinitePresentation (F.obj i) N →
      ∀ (f g : M ⟶ N),
        (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).map f =
          (extendScalars (CommRingCat.Hom.hom (colimit.ι F i))).map g →
        ∃ (j : I) (hij : i ≤ j),
          (extendScalars (CommRingCat.Hom.hom (F.map (homOfLE hij)))).map f =
            (extendScalars (CommRingCat.Hom.hom (F.map (homOfLE hij)))).map g) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro N hN
    let inst : Module.FinitePresentation (colimit F : CommRingCat) N := hN
    obtain ⟨n, m, p, q, hp, hqp⟩ :=
      Module.FinitePresentation.exists_fin' (colimit F : CommRingCat) N
    obtain ⟨i, qi, ⟨e⟩⟩ := exists_stage_finite_relation_cokernel F n m q
    let Q := (Fin n → F.obj i) ⧸ LinearMap.range qi
    let M := ModuleCat.of (F.obj i) (ULift.{v} Q)
    have hQ : Module.FinitePresentation (F.obj i) Q :=
      Module.finitePresentation_of_surjective (LinearMap.range qi).mkQ
        (Submodule.mkQ_surjective _) (by
          rw [Submodule.ker_mkQ]
          exact Submodule.fg_range qi)
    let instQ : Module.FinitePresentation (F.obj i) Q := hQ
    have hM : Module.FinitePresentation (F.obj i) M :=
      Module.FinitePresentation.of_equiv
        (ULift.moduleEquiv : ULift.{v} Q ≃ₗ[F.obj i] Q).symm
    let eN : ModuleCat.of (colimit F : CommRingCat)
        (ULift.{v} ((Fin n → (colimit F : CommRingCat)) ⧸ LinearMap.range q)) ≅ N :=
      ((ULift.moduleEquiv :
        ULift.{v} ((Fin n → (colimit F : CommRingCat)) ⧸ LinearMap.range q) ≃ₗ[_]
          ((Fin n → (colimit F : CommRingCat)) ⧸ LinearMap.range q)).trans
        ((Submodule.quotEquivOfEq (LinearMap.range q) (LinearMap.ker p)
          (LinearMap.exact_iff.mp hqp).symm).trans
          (LinearMap.quotKerEquivOfSurjective p hp))).toModuleIso
    exact ⟨i, M, hM, ⟨e.trans eN⟩⟩
  · intro i M N hM _ f
    let inst : Module.FinitePresentation (F.obj i) M := hM
    let ri := CommRingCat.Hom.hom (colimit.ι F i)
    let h := (extendRestrictScalarsAdj ri).homEquiv _ _ f
    obtain ⟨j, hij, a, ha⟩ := exists_stage_restricted_hom F i M N h
    let rij := CommRingCat.Hom.hom (F.map (homOfLE hij))
    let rj := CommRingCat.Hom.hom (colimit.ι F j)
    have hc : rj.comp rij = ri :=
      congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hij))
    obtain ⟨eM, heM⟩ := exists_comparison ri rij rj hc M
    obtain ⟨eN, heN⟩ := exists_comparison ri rij rj hc N
    let g := ((extendRestrictScalarsAdj rij).homEquiv M _).symm a
    have hg : ∀ m : M, g ((1 : F.obj j) ⊗ₜ[F.obj i, rij] m) = a m := by
      intro m
      have hm := congrArg (fun b => b m)
        (((extendRestrictScalarsAdj rij).homEquiv M _).apply_symm_apply a)
      exact hm
    refine ⟨j, hij, g, eM, eN, heM, heN, ?_⟩
    apply ExtendScalars.hom_ext
    intro m
    change eN.hom (f ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] m)) =
      (extendScalars rj).map g (eM.hom
        ((1 : ↑(colimit F : CommRingCat)) ⊗ₜ[F.obj i, ri] m))
    rw [heM, ExtendScalars.map_tmul, hg]
    exact ha eN heN m
  · intro i M N hM _ f g hfg
    let inst : Module.FinitePresentation (F.obj i) M := hM
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := F.obj i) (M := M)
    let t := s.image (fun m => f m - g m)
    have ht : ∀ n ∈ t,
        (1 : ↑(colimit F)) ⊗ₜ[F.obj i,CommRingCat.Hom.hom (colimit.ι F i)] n = 0 := by
      intro n hn
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hn
      have hm := congrArg (fun b => b
        ((1 : ↑(colimit F)) ⊗ₜ[F.obj i,CommRingCat.Hom.hom (colimit.ι F i)] m)) hfg
      simpa only [ExtendScalars.map_tmul, TensorProduct.tmul_sub, sub_eq_zero] using hm
    obtain ⟨j, hij, hj⟩ := exists_stage_finite_tensor_vanishing F i N t ht
    let rij := CommRingCat.Hom.hom (F.map (homOfLE hij))
    apply Exists.intro j
    apply Exists.intro hij
    apply ((extendRestrictScalarsAdj rij).homEquiv _ _).injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext_on hs
    intro m hm
    have hm' := hj (f m - g m) (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
    change (1 : F.obj j) ⊗ₜ[F.obj i, rij] (f m) =
      (1 : F.obj j) ⊗ₜ[F.obj i, rij] (g m)
    simpa only [TensorProduct.tmul_sub, sub_eq_zero] using hm'

end ModuleCat
