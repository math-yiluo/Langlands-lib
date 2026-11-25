/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.FieldTheory.SeparableExtension

import WeilConjectures.FieldTheory.MakeSeparablyGenerated
import WeilConjectures.AlgebraicGeometry.GenericFibreDominantField
import WeilConjectures.AlgebraicGeometry.PurelyInseparableGenericBaseSpread
import WeilConjectures.AlgebraicGeometry.ReducedGenericFibreFieldEmbedding

/-! # A separating generic field after a radicial base extension

Source: Stacks Project, Tag 0559, second proof, and Tag 030R.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- The reduced generic pullback embeds in a separably generated field after a radicial
base extension. No geometric reducedness of the fibre is asserted here.

Source: Stacks Project, Tag 0559, second proof, and Tag 030R.
Proof: write the base and source as Spec A and Spec B and let K be the fraction field
of A. Localization preserves reducedness, and geometric irreducibility makes B_K a
nonzero domain. Its fraction field L is finitely generated over K. Tag 030R gives a
finite purely inseparable extension K'/K such that the reduced tensor L tensor_K K'
is a separably generated field F over K'. To obtain this from Tag 04KM, take the
compositum in the common purely inseparable upper field. It is a finitely generated
separable subextension of that separably generated extension, so is separably generated.
Scale the finitely many generators b_i of K'/K: if b_i^q = a/d, the element d*b_i has
q-th power a*d^(q-1) in A. Adjoin these scaled elements inside K' to form A'. This
is a finite integral domain with fraction field K', and all its elements have purely
inseparable power equations over A. Thus Spec A' to Spec A is a universal homeomorphism.
Let eta' be its unique point over eta. Localization and reduction commute, identifying
the reduced generic fibre with Spec of (B tensor_A K')_red. The injection B_K into L
remains injective after the flat field extension K'/K. Passing to reductions preserves
injectivity, since nilpotence is detected by an injective ring map. The induced injection
of the reduced generic coordinate ring into F gives a scheme-theoretically dominant
map Spec F to the fibre. It is quasi-compact because both schemes are affine. Its
composite to Spec kappa(eta') is the spectrum map of the displayed field algebra.
In characteristic zero use K'=K; nonemptiness excludes the zero ring in the field
construction. Every scheme is a spectrum or canonical reduction, not arbitrary data
chosen by a definition from an unproved existence statement.

(blueprint: lem-sbc-radicial-separating-generic-field) -/
theorem exists_radicial_separating_generic_field
    {Z S : Scheme.{u}} [IsAffine Z] [IsReduced Z] [IsAffine S] [IsIntegral S]
    (g : Z ⟶ S) [Flat g] [LocallyOfFinitePresentation g]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (g.fiberToSpecResidueField η)) :
    ∃ (S' : Scheme.{u}) (q : S' ⟶ S),
      IsAffine S' ∧ IsIntegral S' ∧ IsUniversalHomeomorphism q ∧
      ∃ η' : S', q η' = η ∧
        ∃ (F : Type u) (hF : Field F) (aF : Algebra (S'.residueField η') F),
          letI := hF
          letI := aF
          ∃ h : Spec (.of F) ⟶
              ((pullback g q).nilradical.subschemeι ≫ pullback.snd g q).fiber η',
            IsSchemeTheoreticallyDominant h ∧ QuasiCompact h ∧
            Algebra.IsSeparablyGenerated (S'.residueField η') F ∧
            h ≫ ((pullback g q).nilradical.subschemeι ≫
              pullback.snd g q).fiberToSpecResidueField η' =
                Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField η') F)) := by
  classical
  obtain ⟨L, hL, aL, hfg, j, hj, hjbase⟩ :=
    exists_generic_fibre_dominant_field g η hη hgeom
  let _ := hL
  let _ := aL
  obtain ⟨k', hk', akk', E, hE, aLE, akE, hfin, hpure, _, _, hsep, hsquare⟩ :=
    FieldExtension.exists_finitePurelyInseparable_separablyGenerated
      (S.residueField η) L hfg
  let _ := hk'
  let _ := akk'
  let _ := hE
  let _ := aLE
  let _ := akE
  have _ := hfin
  have _ := hpure
  obtain ⟨S', q, hA, hI, hU, η', hq, hη', e, he⟩ :=
    exists_purely_inseparable_generic_base_spread η hη k'
  have _ := hA
  have _ := hI
  obtain ⟨aE, h, hdom, hsep', hbase⟩ :=
    exists_reduced_generic_fibre_field_embedding g q η η' hq hη' L k' E
      j hj hjbase e he hsquare hsep
  let _ := aE
  exact ⟨S', q, hA, hI, hU, η', hq, E, hE, aE, h, hdom, inferInstance, hsep', hbase⟩

end AlgebraicGeometry
