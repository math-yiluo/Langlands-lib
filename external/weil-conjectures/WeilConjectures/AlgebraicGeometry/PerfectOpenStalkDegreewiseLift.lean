/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.OpenModuleStalkRestrictionComparison
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.OpenStalkFreeMapLocalLift
import Mathlib.Data.Int.Interval

/-! # Extending degreewise maps between perfect open-site stalks

Source: Stacks Project, Tags 09RE and 01CP.
(blueprint: lem-sc-perfect-open-stalk-degreewise-lift).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Degreewise stalk maps extend on a common affine neighbourhood, without any
chain equations, in the coordinates of the canonical restriction comparison.

Source: Stacks Project, Tag 09RE, affine finite-presentation calculation, and
Tag 01CP, finite-presentation internal-Hom stalk comparison.
(blueprint: lem-sc-perfect-open-stalk-degreewise-lift).

Proof: Pass from the slice site over U to the open subscheme U. The finite-free
retractions make every term of P finitely presented. Apply the internal-Hom stalk
comparison to each component and represent its preimage by a section of internal
Hom near x. Such a section is a local sheaf morphism, giving the required local
map without any finiteness assumption on its target. Outside the finite support interval of P,
use zero maps, since the source is zero.
Intersect the finitely many neighbourhoods, then take an affine neighbourhood W
of x inside the intersection. Restrict all representatives to W. Cofinality of
neighbourhoods inside W and the open-immersion stalk-ring isomorphisms give a
natural isomorphism `openModuleStalkRestrictionComparison` between restriction
followed by the W stalk and the U stalk; apply it termwise to obtain e. The germ
formulas give the stated component
identities. Empty source support intervals and zero ranks require no representatives
and give the zero family. No perfectness assumption on Q or affineness
assumption on U is needed. No differential compatibility is imposed or asserted. -/
theorem exists_affine_perfect_open_stalk_degreewise_lift
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hxU : x ∈ U)
    (P Q : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hP : IsStrictlyPerfect X U P)
    (t : ∀ n : ℤ,
      (((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj P).X n ⟶
      (((openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)).obj Q).X n) :
    ∃ (W : X.Opens) (hxW : x ∈ W) (_hW : IsAffineOpen W) (hWU : W ≤ U),
      let R := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE hWU : W ⟶ U)).mapHomologicalComplex (.up ℤ)
      let S := (openModuleStalkFunctor X W ⟨x, hxW⟩).mapHomologicalComplex (.up ℤ)
      let T := (openModuleStalkFunctor X U ⟨x, hxU⟩).mapHomologicalComplex (.up ℤ)
      let e : R ⋙ S ≅ T := Functor.mapHomologicalComplexCompIso
        (openModuleStalkRestrictionComparison X U W hWU x hxU hxW) (.up ℤ)
      ∃ g : ∀ n : ℤ, (R.obj P).X n ⟶ (R.obj Q).X n,
        ∀ n : ℤ, (openModuleStalkFunctor X W ⟨x, hxW⟩).map (g n) =
          (e.app P).hom.f n ≫ t n ≫ (e.app Q).inv.f n := by
  classical
  obtain ⟨a, b, hzero⟩ := hP.1
  choose m ι π hιπ using hP.2
  let T := openModuleStalkFunctor X U ⟨x, hxU⟩
  have he := exists_open_stalk_free_map_local_lifts X U x hxU
  have lifts (n : ℤ) := he (m n) (Q.X n) (T.map (π n) ≫ t n)
  choose V hxV hVU lift using lifts
  let I := {n : ℤ // n ∈ Finset.Icc a b}
  let D : X.Opens := U ⊓ ⨅ n : I, V n.val
  have hxD : x ∈ D := by
    refine ⟨hxU, ?_⟩
    change x ∈ (↑(⨅ n : I, V n.val) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun n ↦ hxV n.val)
  obtain ⟨W, hW, hxW, hWD⟩ := exists_isAffineOpen_mem_and_subset hxD
  have hWU : W ≤ U := le_trans hWD inf_le_left
  have hWV (n : I) : W ≤ V n.val :=
    le_trans hWD (inf_le_right.trans (iInf_le _ n))
  let R := SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE hWU)
  let S := openModuleStalkFunctor X W ⟨x, hxW⟩
  let eW := openModuleStalkRestrictionComparison X U W hWU x hxU hxW
  choose f hf using (fun n : I ↦ lift n.val W hxW (hWV n) hWU)
  let g (n : ℤ) : R.obj (P.X n) ⟶ R.obj (Q.X n) :=
    if hn : n ∈ Finset.Icc a b then R.map (ι n) ≫ f ⟨n, hn⟩ else 0
  refine ⟨W, hxW, hW, hWU, g, ?_⟩
  intro n
  change S.map (g n) = eW.hom.app (P.X n) ≫ t n ≫ eW.inv.app (Q.X n)
  by_cases hn : n ∈ Finset.Icc a b
  · dsimp only [g]
    rw [dite_eq_left hn, S.map_comp, hf ⟨n, hn⟩]
    have hnat := eW.hom.naturality (ι n)
    change S.map (R.map (ι n)) ≫ eW.hom.app _ =
      eW.hom.app _ ≫ T.map (ι n) at hnat
    calc
      S.map (R.map (ι n)) ≫
          (eW.hom.app _ ≫ (T.map (π n) ≫ t n) ≫ eW.inv.app _) =
          (S.map (R.map (ι n)) ≫ eW.hom.app _) ≫
            T.map (π n) ≫ t n ≫ eW.inv.app _ := by simp only [Category.assoc]
      _ = (eW.hom.app _ ≫ T.map (ι n)) ≫
          T.map (π n) ≫ t n ≫ eW.inv.app _ := by rw [hnat]
      _ = eW.hom.app _ ≫ t n ≫ eW.inv.app _ := by
        rw [Category.assoc, ← Category.assoc (T.map (ι n)), ← T.map_comp, hιπ n,
          T.map_id, Category.id_comp]
  · have hz : IsZero (P.X n) := hzero n (by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      exact hn)
    have ht : t n = 0 := (T.map_isZero hz).eq_of_src _ _
    dsimp only [g]
    rw [dite_eq_right hn, S.map_zero, ht, zero_comp, comp_zero]

end
end AlgebraicGeometry.Scheme
