import Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension

/-!
# Extension of scalars of the smooth part

For an algebra `R → S` of commutative rings and a topological group `G`, the inclusion of the
smooth vectors `V^sm → V` of a representation, tensored with `S`, is a map
`S ⊗[R] V^sm → S ⊗[R] V` out of a smooth representation, so it factors through the smooth part
`(S ⊗[R] V)^sm`. This gives a natural map `S ⊗[R] V^sm → (S ⊗[R] V)^sm` of smooth
representations, its degreewise version on complexes, and its value on Harris's inverse-limit
complex, also for the actual coefficient rings `CoefficientIntegers l → FiniteCompletion L l`.
See `SmoothPartScalarExtension.md`.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory TensorProduct

universe w uR uS uG

section Generic

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The natural map `S ⊗[R] V^sm → (S ⊗[R] V)^sm`, `s ⊗ v ↦ s ⊗ v`: the extension of scalars of
the inclusion of smooth vectors `V^sm → V`, a map out of the smooth representation
`S ⊗[R] V^sm`, corresponds under the smooth-part adjunction to a map into the smooth part. -/
def smoothPartExtendScalars :
    SmoothRep.smoothPartFunctor.{uR, uG, w} R G ⋙ smoothRepExtendScalars.{w} R S G ⟶
      repExtendScalars.{w} R S G ⋙ SmoothRep.smoothPartFunctor.{uS, uG, max uS w} S G where
  app V := (SmoothRep.toRepSmoothPartAdjunction S G).homEquiv _ _
    ((repExtendScalars R S G).map ((SmoothRep.toRepSmoothPartAdjunction R G).counit.app V))
  naturality _ _ f :=
    (SmoothRep.toRepSmoothPartAdjunction S G).homEquiv_naturality_left_square _ _ _ _
      (((repExtendScalars R S G).map_comp _ _).symm.trans
        ((congrArg (repExtendScalars R S G).map
          ((SmoothRep.toRepSmoothPartAdjunction R G).counit_naturality f)).trans
          ((repExtendScalars R S G).map_comp _ _)))

@[simp]
theorem smoothPartExtendScalars_app_tmul (V : Rep.{w} R G) (s : S) (v : smoothVectors V.ρ) :
    (SmoothRep.hom ((smoothPartExtendScalars.{w} R S G).app V) (s ⊗ₜ[R] v)).val =
      s ⊗ₜ[R] v.val := rfl

/-- Followed by the inclusion of smooth vectors of `S ⊗[R] V`, the map
`smoothPartExtendScalars` is the extension of scalars of the inclusion of smooth vectors
of `V`. -/
theorem smoothPartExtendScalars_app_comp_counit (V : Rep.{w} R G) :
    SmoothRep.toRep.map ((smoothPartExtendScalars.{w} R S G).app V) ≫
        (SmoothRep.toRepSmoothPartAdjunction S G).counit.app ((repExtendScalars R S G).obj V) =
      (repExtendScalars R S G).map ((SmoothRep.toRepSmoothPartAdjunction R G).counit.app V) :=
  ((SmoothRep.toRepSmoothPartAdjunction S G).homEquiv_counit _ _ _).symm.trans
    (Equiv.symm_apply_apply _ _)

variable {ι : Type*} (c : ComplexShape ι)

/-- The degreewise map `S ⊗[R] K^sm → (S ⊗[R] K)^sm`, a natural chain map from the extension of
scalars of the smooth part of a complex to the smooth part of its extension of scalars. -/
def smoothPartComplexExtendScalars :
    smoothPartComplex.{w} R G c ⋙ smoothRepExtendScalarsComplex.{w} R S G c ⟶
      repExtendScalarsComplex.{w} R S G c ⋙ smoothPartComplex.{max uS w} S G c where
  app K :=
    { f i := (smoothPartExtendScalars R S G).app (K.X i)
      comm' i j _ := ((smoothPartExtendScalars R S G).naturality (K.d i j)).symm }
  naturality _ _ φ :=
    HomologicalComplex.hom_ext _ _ fun i => (smoothPartExtendScalars R S G).naturality (φ.f i)

/-- Followed by the degreewise inclusion of smooth vectors of `S ⊗[R] K`, the chain map
`smoothPartComplexExtendScalars` is the extension of scalars of the degreewise inclusion of
smooth vectors of `K`. -/
theorem smoothPartComplexExtendScalars_app_comp_inclusion (K : HomologicalComplex (Rep.{w} R G) c) :
    ((SmoothRep.toRep (R := S) (G := G)).mapHomologicalComplex c).map
        ((smoothPartComplexExtendScalars.{w} R S G c).app K) ≫
        (smoothPartComplexInclusion S G c).app ((repExtendScalarsComplex R S G c).obj K) =
      (repExtendScalarsComplex R S G c).map ((smoothPartComplexInclusion R G c).app K) :=
  HomologicalComplex.hom_ext _ _ fun i => smoothPartExtendScalars_app_comp_counit R S G (K.X i)

end Generic

namespace DivisibleSystem

section Harris

variable {R : Type uR} [CommRing R] (S : Type uR) [CommRing S] [Algebra R S] {G : Type uG}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ℓ : ℕ}
  (N : ℕ) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  {ι : Type uG} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H) [∀ i, (H i).Normal]
  [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)] [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map ((K.projection h).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- The degreewise smooth part of `quotientInvariantsInverseLimit`. -/
abbrev quotientInvariantsInverseLimitSmooth :
    CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℤ :=
  (smoothPartComplex.{max w uR uG} R G (ComplexShape.up ℤ)).obj
    (quotientInvariantsInverseLimit.{w, uR, uG} N K H hH hK hk)

/-- The degreewise inclusion of `quotientInvariantsInverseLimitSmooth` into
`quotientInvariantsInverseLimit`. -/
abbrev quotientInvariantsInverseLimitSmoothInclusion :
    ((SmoothRep.toRep (R := R) (G := G)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (quotientInvariantsInverseLimitSmooth.{w, uR, uG} N K H hH hK hk) ⟶
      quotientInvariantsInverseLimit.{w, uR, uG} N K H hH hK hk :=
  (smoothPartComplexInclusion.{max w uR uG} R G (ComplexShape.up ℤ)).app
    (quotientInvariantsInverseLimit.{w, uR, uG} N K H hH hK hk)

/-- The degreewise extension of scalars `S ⊗[R] -` of `quotientInvariantsInverseLimitSmooth`, a
complex of smooth representations over `S`. -/
abbrev quotientInvariantsInverseLimitSmoothBaseChange :
    CochainComplex (SmoothRep.{uR, uG, max w uR uG} S G) ℤ :=
  (smoothRepExtendScalarsComplex.{max w uR uG} R S G (ComplexShape.up ℤ)).obj
    (quotientInvariantsInverseLimitSmooth.{w, uR, uG} N K H hH hK hk)

/-- The chain map `smoothPartComplexExtendScalars` from
`quotientInvariantsInverseLimitSmoothBaseChange` (smooth part, then `S ⊗[R] -`) to
`quotientInvariantsInverseLimitBaseChangeSmooth` (`S ⊗[R] -`, then smooth part). -/
abbrev quotientInvariantsInverseLimitSmoothBaseChangeMap :
    quotientInvariantsInverseLimitSmoothBaseChange.{w, uR, uG} S N K H hH hK hk ⟶
      quotientInvariantsInverseLimitBaseChangeSmooth.{w, uR, uG} S N K H hH hK hk :=
  (smoothPartComplexExtendScalars.{max w uR uG} R S G (ComplexShape.up ℤ)).app
    (quotientInvariantsInverseLimit.{w, uR, uG} N K H hH hK hk)

/-- Followed by `quotientInvariantsInverseLimitBaseChangeSmoothInclusion`, the chain map
`quotientInvariantsInverseLimitSmoothBaseChangeMap` is the extension of scalars of
`quotientInvariantsInverseLimitSmoothInclusion`. -/
theorem quotientInvariantsInverseLimitSmoothBaseChangeMap_comp_inclusion :
    ((SmoothRep.toRep (R := S) (G := G)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (quotientInvariantsInverseLimitSmoothBaseChangeMap.{w, uR, uG} S N K H hH hK hk) ≫
        quotientInvariantsInverseLimitBaseChangeSmoothInclusion.{w, uR, uG} S N K H hH hK hk =
      (repExtendScalarsComplex.{max w uR uG} R S G (ComplexShape.up ℤ)).map
        (quotientInvariantsInverseLimitSmoothInclusion.{w, uR, uG} N K H hH hK hk) :=
  smoothPartComplexExtendScalars_app_comp_inclusion.{max w uR uG} R S G (ComplexShape.up ℤ)
    (quotientInvariantsInverseLimit.{w, uR, uG} N K H hH hK hk)

end Harris

section Coefficients

open Langlands.Global Langlands.Shimura.Coefficients

variable {L : Type uR} [Field L] [NumberField L] (l : FinitePlace L) {G : Type uG} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] {ℓ : ℕ} (N : ℕ)
  (K : DivisibleSystem
    (CochainComplex (SmoothRep.{uR, uG, max w uR uG} (CoefficientIntegers l) G) ℕ) ℓ)
  {ι : Type uG} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H) [∀ i, (H i).Normal]
  [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)] [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants (CoefficientIntegers l) (H i)).map ((K.projection h).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j),
    IsUnit (Nat.card (quotientProjection (hH hij)).ker : CoefficientIntegers l))
  [IsFiltered ι]

/-- `quotientInvariantsInverseLimitSmoothBaseChange` for coefficients in the actual local ring of
integers `CoefficientIntegers l` at a finite place `l` of a number field `L`, extended to the
completion `FiniteCompletion L l`. -/
abbrev quotientInvariantsInverseLimitSmoothCompletion :
    CochainComplex (SmoothRep.{uR, uG, max w uR uG} (FiniteCompletion L l) G) ℤ :=
  quotientInvariantsInverseLimitSmoothBaseChange.{w, uR, uG} (FiniteCompletion L l) N K H hH hK hk

/-- `quotientInvariantsInverseLimitSmoothBaseChangeMap` for `CoefficientIntegers l` and
`FiniteCompletion L l`: the chain map from `quotientInvariantsInverseLimitSmoothCompletion` to
`quotientInvariantsInverseLimitCompletionSmooth`. -/
abbrev quotientInvariantsInverseLimitSmoothCompletionMap :
    quotientInvariantsInverseLimitSmoothCompletion.{w, uR, uG} l N K H hH hK hk ⟶
      quotientInvariantsInverseLimitCompletionSmooth.{w, uR, uG} l N K H hH hK hk :=
  quotientInvariantsInverseLimitSmoothBaseChangeMap.{w, uR, uG} (FiniteCompletion L l) N K H hH
    hK hk

/-- `quotientInvariantsInverseLimitSmoothBaseChangeMap_comp_inclusion` for
`CoefficientIntegers l` and `FiniteCompletion L l`. -/
theorem quotientInvariantsInverseLimitSmoothCompletionMap_comp_inclusion :
    ((SmoothRep.toRep (R := FiniteCompletion L l) (G := G)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        (quotientInvariantsInverseLimitSmoothCompletionMap.{w, uR, uG} l N K H hH hK hk) ≫
        quotientInvariantsInverseLimitCompletionSmoothInclusion.{w, uR, uG} l N K H hH hK hk =
      (repExtendScalarsComplex.{max w uR uG} (CoefficientIntegers l) (FiniteCompletion L l) G
        (ComplexShape.up ℤ)).map
        (quotientInvariantsInverseLimitSmoothInclusion.{w, uR, uG} N K H hH hK hk) :=
  quotientInvariantsInverseLimitSmoothBaseChangeMap_comp_inclusion.{w, uR, uG}
    (FiniteCompletion L l) N K H hH hK hk

end Coefficients

end DivisibleSystem

end Langlands.Cohomology
