/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.AlgebraicGeometry.CommonGenericHypersurfaceAffineOpen
import WeilConjectures.AlgebraicGeometry.GenericHypersurfaceGeometricIrreducibilitySpread

/-! # A spreading affine chart of a generically geometrically integral family

Source: Stacks Project, Tags 0559 and 0557, the common hypersurface open.
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A generically geometrically integral affine family contains an affine open
whose geometric fibres are irreducible near the generic point. This only controls
the open subfamily; it makes no assertion about the rest of the source fibres.

Source: Stacks Project, Tag 0559, the separating transcendence basis and common
open construction; Tag 0557, spreading an absolutely irreducible polynomial.
Proof: write the integral affine base as Spec A and the reduced affine source as
Spec B. Flatness makes B embed in its generic fibre, which is a geometrically
integral domain. The fraction field L of that domain is a regular finitely
generated extension of K=Frac A. A separating transcendence basis and a primitive
element give L=K(x_1,...,x_r)[x_(r+1)] with an absolutely irreducible minimal
polynomial. Take its primitive numerator over K and clear base denominators
to obtain P over A. After a base localization and the monic change of variables
described below, the hypersurface ring embeds in its generic fibre and is a
domain. After shrinking the base,
the hypersurface Spec(A[x_1,...,x_(r+1)]/(P)) and Spec B have isomorphic nonempty
affine opens over A: write the finitely many generators of each algebra as
fractions in their common function field and invert their denominators. Spread
absolute irreducibility of P by Tag 0557: a triangular substitution by separated
powers makes P monic in its last variable after inverting its leading
coefficient. For each positive pair of possible factor degrees, bounded-degree
monic factor coefficients and the coefficient equations for their product form
a finite type algebra. There is no point of its generic fibre over the algebraic
closure, so Nullstellensatz makes that fibre zero. Inverting a nonzero base
element kills this algebra. Invert the finite product of those elements. Now P
is irreducible over every algebraically closed residue field, and the
hypersurface fibres are geometrically integral. Its common affine open W is
therefore geometrically irreducible whenever nonempty. Generic flatness of W
and its finite presentation make its image open; shrink to this image to ensure
nonemptiness of every fibre. Choose a further affine base neighbourhood and
view W as an affine open in the original source. All shrinkings contain the
generic point. Relative dimension zero uses a linear polynomial, so the set of
positive factor-degree pairs is empty. Empty source is excluded by the generic
irreducibility hypothesis.

(blueprint: lem-sbc-generic-geometrically-integral-affine-chart) -/
theorem exists_generic_geometrically_integral_affine_chart
    {X S : Scheme.{u}} [IsAffine X] [IsReduced X] [IsAffine S] [IsIntegral S]
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η))
    (hred : GeometricallyReduced (f.fiberToSpecResidueField η)) :
    ∃ W : X.Opens, IsAffineOpen W ∧ ∃ U : S.Opens, η ∈ U ∧
      ∀ s, s ∈ U → GeometricallyIrreducible ((W.ι ≫ f).fiberToSpecResidueField s) := by
  obtain ⟨W, hW, hηW, n, P, i, hi, hif, hgeomH, hredH⟩ :=
    exists_common_generic_hypersurface_affine_open f η hη hgeom hred
  let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
  let g : H ⟶ S := Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
  change i ≫ g = W.ι ≫ f at hif
  change IsOpenImmersion i at hi
  have := hi
  obtain ⟨U, hηU, hU⟩ :=
    exists_open_generic_hypersurface_geometric_irreducibility n P η hη hgeomH hredH
  let V : S.Opens := ⟨Set.range (W.ι ≫ f), (W.ι ≫ f).isOpenMap.isOpen_range⟩
  refine ⟨W, hW, U ⊓ V, ⟨hηU, hηW⟩, ?_⟩
  intro s hs
  have := hU s hs.1
  have hne : Nonempty ((W.ι ≫ f).fiber s) := by
    apply ((W.ι ≫ f).fiberHomeo s).nonempty_congr.mpr
    obtain ⟨w, hw⟩ := hs.2
    exact ⟨⟨w, hw⟩⟩
  let j : (W.ι ≫ f).fiber s ⟶ g.fiber s :=
    Limits.pullback.map (W.ι ≫ f) (S.fromSpecResidueField s) g
      (S.fromSpecResidueField s) i (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using hif.symm) (by simp)
  have hj : IsOpenImmersion j := by infer_instance
  have hjf : j ≫ g.fiberToSpecResidueField s =
      (W.ι ≫ f).fiberToSpecResidueField s := by
    simp [j, Scheme.Hom.fiberToSpecResidueField]
  have hsurj : Surjective (j ≫ g.fiberToSpecResidueField s) := by
    exact ⟨fun t ↦ ⟨Nonempty.some hne, Subsingleton.elim _ _⟩⟩
  rw [← hjf]
  infer_instance

end AlgebraicGeometry
