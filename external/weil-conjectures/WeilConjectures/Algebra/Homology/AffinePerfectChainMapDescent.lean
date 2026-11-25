/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs

import WeilConjectures.Algebra.Homology.BoundedGradedMapColimitDescent
import WeilConjectures.Algebra.Homology.FiniteChainSquaresColimitDescent

/-! # Descent of chain maps between affine perfect complexes

Source: Stacks Project, Tag 09RE, affine case (1).
(blueprint: lem-pc-affine-perfect-chain-map-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A graded map conjugate to a chain map satisfies the chain-map equations. -/
private theorem graded_comm_of_conjugate
    {R : Type u} [CommRing R]
    {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (eP : P ≅ P') (eQ : Q ≅ Q')
    (v : ∀ n : ℤ, P'.X n ⟶ Q'.X n) (f : P ⟶ Q)
    (hv : ∀ n : ℤ, eP.hom.f n ≫ v n ≫ eQ.inv.f n = f.f n)
    (m n : ℤ) : v m ≫ Q'.d m n = P'.d m n ≫ v n := by
  apply (cancel_epi (eP.hom.f m)).1
  apply (cancel_mono (eQ.inv.f n)).1
  calc
    (eP.hom.f m ≫ (v m ≫ Q'.d m n)) ≫ eQ.inv.f n =
        (eP.hom.f m ≫ v m ≫ eQ.inv.f m) ≫ Q.d m n := by
      simp only [Category.assoc, ← eQ.inv.comm m n]
    _ = f.f m ≫ Q.d m n := by rw [hv m]
    _ = P.d m n ≫ f.f n := f.comm m n
    _ = (eP.hom.f m ≫ (P'.d m n ≫ v n)) ≫ eQ.inv.f n := by
      rw [← hv n]
      simp only [Category.assoc, eP.hom.comm_assoc m n]

/-- Chain maps between the limit base changes of bounded finite projective complexes
are scalar extensions of chain maps at some later stage.

Source: Stacks Project, Tag 09RE, affine case (1); Tag 05N7 for finite-presentation descent.
Proof: Finite projective terms are finitely presented by Mathlib. Use
`exists_bounded_graded_map_of_directed_colimit` to descend the components in the
finite support of E₀, without yet requiring chain-map equations. Conjugation by
the canonical scalar-extension isomorphisms identifies the extended components
with f. Cancelling those isomorphisms and using their differential naturality
proves that all chain squares commute over the colimit. Apply
`eventually_commuting_finite_chain_squares` to the finitely many squares whose
source degree lies in the support interval. Outside that interval extension of
scalars preserves the zero source, so the equations hold automatically. These
components define g. The two componentwise comparison equalities compose, and
unfolding `scalarExtensionHom` and componentwise extensionality give its required
equality with f. The two descent lemmas handle directed preorders; no partial-order
assumption is added here.
(blueprint: lem-pc-affine-perfect-chain-map-descent) -/
theorem affine_perfect_chainMap_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{u}) (i₀ : I)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ)
    (hE : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (E₀.X n) ∧
        Module.Projective (F.obj i₀) (E₀.X n))
    (hK : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (F.obj i₀) (K₀.X n) ∧
        Module.Projective (F.obj i₀) (K₀.X n))
    (f : ((ModuleCat.extendScalars (colimit.ι F i₀).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀ ⟶
      ((ModuleCat.extendScalars (colimit.ι F i₀).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀) :
    ∃ (i : Set.Ici i₀)
      (g : ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj E₀ ⟶
        ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).mapHomologicalComplex
          (.up ℤ)).obj K₀),
      scalarExtensionHom (F.map (homOfLE i.property)).hom (colimit.ι F i.val).hom
        (colimit.ι F i₀).hom
        (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE i.property)).symm)
        E₀ K₀ g = f := by
  obtain ⟨a, b, hzero⟩ := hE.1
  have hEfp (n : ℤ) : Module.FinitePresentation (F.obj i₀) (E₀.X n) := by
    let := (hE.2 n).1
    let := (hE.2 n).2
    exact Module.finitePresentation_of_projective (F.obj i₀) (E₀.X n)
  have hKfp (n : ℤ) : Module.FinitePresentation (F.obj i₀) (K₀.X n) := by
    let := (hK.2 n).1
    let := (hK.2 n).2
    exact Module.finitePresentation_of_projective (F.obj i₀) (K₀.X n)
  let e (t : Set.Ici i₀) (C : CochainComplex (ModuleCat.{u} (F.obj i₀)) ℤ) :=
    eqToIso (congrArg (fun r ↦
      ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj C)
      (congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE t.property)).symm)) ≪≫
    (NatIso.mapHomologicalComplex
      (ModuleCat.extendScalarsComp (F.map (homOfLE t.property)).hom
        (colimit.ι F t.val).hom) (.up ℤ)).app C
  obtain ⟨i, v, hv⟩ :=
    exists_bounded_graded_map_of_directed_colimit F i₀ E₀ K₀ a b hzero hEfp hKfp f.f
  have hcomm (n : ℤ) :
      (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v n) ≫
        (ModuleCat.extendScalars (colimit.ι F i.val).hom).map
          ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).map
            (K₀.d n (n + 1))) =
      (ModuleCat.extendScalars (colimit.ι F i.val).hom).map
          ((ModuleCat.extendScalars (F.map (homOfLE i.property)).hom).map
            (E₀.d n (n + 1))) ≫
        (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v (n + 1)) := by
    exact graded_comm_of_conjugate (e i E₀) (e i K₀)
      (fun n ↦ (ModuleCat.extendScalars (colimit.ι F i.val).hom).map (v n))
      f hv n (n + 1)
  obtain ⟨j, _, w, hw, hext⟩ :=
    eventually_commuting_finite_chain_squares F i₀ E₀ K₀ hEfp hKfp i v a b
      (fun n _ _ ↦ hcomm n)
  let G := ModuleCat.extendScalars (F.map (homOfLE j.property)).hom
  let g : (G.mapHomologicalComplex (.up ℤ)).obj E₀ ⟶
      (G.mapHomologicalComplex (.up ℤ)).obj K₀ :=
    { f := w
      comm' := by
        intro m n hmn
        have hn : m + 1 = n := hmn
        subst n
        by_cases hm : a ≤ m ∧ m ≤ b
        · exact hw m hm.1 hm.2
        · have hz : IsZero (G.obj (E₀.X m)) := G.map_isZero (hzero m (by omega))
          exact hz.eq_of_src _ _ }
  refine ⟨j, g, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  have hn := (hext n).trans (hv n)
  change (e j E₀).hom.f n ≫
    (ModuleCat.extendScalars (colimit.ι F j.val).hom).map (w n) ≫
      (e j K₀).inv.f n = f.f n at hn
  simpa only [scalarExtensionHom, e, Iso.trans_hom, Iso.trans_inv,
    eqToIso.hom, eqToIso.inv, Iso.app_hom, Iso.app_inv,
    HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, g, Category.assoc] using hn

end CochainComplex
