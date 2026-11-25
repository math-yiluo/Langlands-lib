/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Blowup.Affine.ReesGrading
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

import WeilConjectures.AlgebraicGeometry.IdealPowersReesMultiplicationComponent

/-! # Multiplication maps on ideal powers

Source: Stacks Project, coherent.tex, Tag 02O8, proof and preceding paragraph.
-/

@[expose] public section

set_option autoImplicit false
universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Multiplication by a homogeneous Rees coefficient lifts to the ideal-power products.
Source: Stacks Project, coherent.tex, Tag 02O8, lines 5330--5400.
(blueprint: lem-weil-pbc-ideal-powers-rees-multiplication).

Proof: Write a homogeneous polynomial b as a t^k with a in I^k. The inclusion
J^m F into F is a monomorphism. Locally every section of J^m F is a finite sum
of products of m local sections of J with sections of F. Since J is the extended
ideal, multiplication by the image of a sends such a section into J^(m+k) F:
expand a as a sum of products of k elements of I and concatenate the factors.
This can be checked on an affine cover by the ideal-product and extended-ideal
section formulas. The lifts are unique under the monomorphic inclusion, hence
agree on intersections and glue on every open. Additivity, O_X-linearity, and
compatibility with restrictions follow after the same inclusion, and give the
required module-sheaf morphisms. Properness and Noetherianity are unnecessary.
For k=0 it is ordinary scalar multiplication; zero and unit ideals cause no
exception because I^0=A. The empty scheme gives the unique maps. -/
theorem idealPowersReesMultiplication {A : Type v} [CommRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    (I : Ideal A) (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) [F.IsQuasicoherent] :
    let G := fun m ↦ Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F
    let graded := reesGrading I
    ∃ mu : ∀ (m k : ℕ), graded k → (G m ⟶ G (m + k)),
      (∀ (m k : ℕ) (b : graded k) (U : X.Opens) (s : (G m).val.obj (op U)),
        ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (m + k)).2 F).app
          U).hom ((mu m k b).app U s) =
        (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top).hom
          (b.val.val.coeff k)) •
        ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι m).2 F).app
          U).hom s) := by
  classical
  dsimp
  let G := fun m ↦ Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F
  let graded := reesGrading I
  have h := idealPowersReesMultiplication_component f I J hJ F
  choose mu hmu using h
  exact ⟨mu, fun m k b U s => hmu m k b U s⟩

end AlgebraicGeometry
