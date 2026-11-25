/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.AlgebraicGeometry.SupportedCompactDetectorModel
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.GeneratorTowerNormalize

/-! # Telescope construction for a given supported compact detector

Source: Stacks Project, duality.tex, proof of Lemma 48.4.3(3), Section Tag 0E4G;
derived.tex, lemma-write-as-colimit (Tag 09SN).
(blueprint: lem-sc-supported-derived-generated-perfect-core).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

/-- A given compact supported detector builds each supported quasi-coherent object.
Source: Stacks Project, duality.tex, proof of Lemma 48.4.3(3), Section Tag 0E4G;
derived.tex, lemma-write-as-colimit (Tag 09SN).
(blueprint: lem-sc-supported-derived-generated-perfect-core).

Proof:
1. Let P be the ambient object property of quasi-coherent cohomology with zero stalks
   on V. The supplied triangulated-closure hypothesis equips its full subcategory
   with the inherited triangulated structure. The support hypothesis puts E in it.
2. Ambient coproducts have coproduct cohomology by
   `lem-pc-derived-ambient-direct-sums`. By `lem-pc-stalk-direct-sums`, their stalks
   on V are sums of zero modules and hence zero. Quasi-coherence is preserved by
   `lem-pc-derived-qcoh-direct-sums`. Thus P has coproducts created by its inclusion.
3. The supplied compactness of E in D_QCoh(Y), fullness, and the agreement of
   coproducts make E compact in P. The supplied shifted-Hom detection
   equivalence gives the singleton generating family in `def-pc-generators`.
4. The small-site K-injective resolutions of `prop-pur-kinjective-resolutions-exist`
   show that derived Hom sets are u-small: after resolving the target, morphisms
   are homotopy classes of chain maps between sheaves of modules in universe u.
   Surjectivity of the localization map into a K-injective target gives smallness
   as a quotient of this u-small chain-map set. Replace P by its equivalent model
   with these small Hom sets. Apply `lem-pc-compact-generators-build-objects` with
   coproduct universe u to the singleton family and Q, then transport back to P.
   Write its sequence as A_n and its triangles as Z_n -> A_n -> A_(n+1) -> Z_n[1].
   Rotate each triangle once. Since the shift functor is an equivalence, it preserves
   coproducts, so Z_n[1] is a coproduct of E[m+1]. Fullness transports these triangles
   and the telescope triangle to the ambient derived category.
5. Set X_0=0 and X_(n+1)=A_n. The first triangle is the distinguished triangle
   0 -> A_0 -> A_0 -> 0[1]; all other triangles are those from step 4. A coproduct
   of the X_n is isomorphic to the coproduct of the A_n: the new summand is zero,
   and all other summands are relabelled by n+1. Under this isomorphism the endomorphism
   s induced by the transitions becomes the old shift endomorphism (on the zero
   summand both maps are zero). Transporting the telescope triangle along this
   isomorphism gives the asserted triangle with 1-s. Replace ULift-indexed sums
   by naturally indexed cofans using the index equivalence. The full subcategory
   objects supply the required quasi-coherent X_n. -/
theorem supported_derived_generated_perfect_core (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (V : Y.Opens) (E Q : schemeDerivedQCohCategory Y)
    (htri : ObjectProperty.IsTriangulated (fun K : schemeDerivedCategory Y ↦
      schemeDerivedQCohProperty Y K ∧
        ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj K).val.presheaf y))))
    (hcompact :
      letI : HasCoproducts.{u} (schemeDerivedQCohCategory Y) := derivedQCohDirectSums Y
      IsCompactObject E)
    (hsupport : ∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj E.obj).val.presheaf y)))
    (hgen : ∀ K : schemeDerivedQCohCategory Y,
      (∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj K.obj).val.presheaf y))) →
      (IsZero K.obj ↔ ∀ n : ℤ, Subsingleton (E.obj⟦n⟧ ⟶ K.obj))) :
    (∀ (k : ℤ) (y : Y), y ∉ (V : Set Y)ᶜ →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) k).obj Q.obj).val.presheaf y))) →
      ∃ (X : ℕ → schemeDerivedQCohCategory Y)
        (t : ∀ n : ℕ, (X n).obj ⟶ (X (n + 1)).obj),
        IsZero (X 0).obj ∧
        (∀ n : ℕ, ∃ (I : Type u) (m : I → ℤ)
          (C : Cofan (fun i : I ↦ E.obj⟦m i⟧)), Nonempty (IsColimit C) ∧
          ∃ (a : (X (n + 1)).obj ⟶ C.pt)
            (b : C.pt ⟶ (X n).obj⟦(1 : ℤ)⟧),
            Triangle.mk (t n) a b ∈ distTriang (schemeDerivedCategory Y)) ∧
        ∃ (S : Cofan (fun n : ℕ ↦ (X n).obj)), Nonempty (IsColimit S) ∧
          ∃ (s : S.pt ⟶ S.pt) (q : S.pt ⟶ Q.obj)
            (r : Q.obj ⟶ S.pt⟦(1 : ℤ)⟧),
            (∀ n : ℕ, S.inj n ≫ s = t n ≫ S.inj (n + 1)) ∧
            Triangle.mk (𝟙 S.pt - s) q r ∈ distTriang (schemeDerivedCategory Y) := by
  intro hQ
  obtain ⟨C, cat, z, shift, add, shiftAdd, pretri, tri, sums, F, comm,
    htriF, haddF, hsumF, hqcF, e, q, ⟨he⟩, ⟨hq⟩, hecompact, hegen⟩ :=
    supported_compact_detector_model Y V E Q htri hcompact hsupport hgen hQ
  let := cat
  let := z
  let := shift
  let := add
  let := shiftAdd
  let := pretri
  let := tri
  let := sums
  let := comm
  let := htriF
  let := haddF
  obtain ⟨A, t, hstart, hsteps, qA, rA, htel⟩ :=
    compactGenerators_buildObjects.{u, u} (fun _ : ULift.{u} Unit ↦ e)
      (fun _ ↦ hecompact) hegen q
  have hstart' : ∃ (J : Type u) (m : J → ℤ),
      Nonempty (A 0 ≅ ∐ fun j : J ↦ e⟦m j⟧) := by
    obtain ⟨J, _, m, h⟩ := hstart
    exact ⟨J, m, h⟩
  have hsteps' : ∃ (Z : ℕ → C) (a : ∀ n : ℕ, Z n ⟶ A n)
      (b : ∀ n : ℕ, A (n + 1) ⟶ (Z n)⟦(1 : ℤ)⟧),
      (∀ n : ℕ, ∃ (J : Type u) (m : J → ℤ),
        Nonempty (Z n ≅ ∐ fun j : J ↦ e⟦m j⟧)) ∧
      ∀ n : ℕ, Triangle.mk (a n) (t n) (b n) ∈ distTriang C := by
    obtain ⟨Z, a, b, hZ, hdist⟩ := hsteps
    refine ⟨Z, a, b, ?_, hdist⟩
    intro n
    obtain ⟨J, _, m, h⟩ := hZ n
    exact ⟨J, m, h⟩
  obtain ⟨X, tX, hzero, htrans, hcolim⟩ :=
    generator_tower_normalize F hsumF e q E.obj Q.obj he hq
      A t hstart' hsteps' qA rA htel
  exact ⟨fun n ↦ ⟨F.obj (X n), hqcF (X n)⟩, tX, hzero, htrans, hcolim⟩

end AlgebraicGeometry
