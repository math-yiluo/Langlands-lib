import Langlands.Cohomology.DivisibleSystem.ConstantInverseLimit
import Langlands.Cohomology.HyperextScalarExtension
import Mathlib.RingTheory.Flat.Localization

/-!
# Integral and rational structures on the `ℓ`-adic limits of smooth Godement towers

Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half spaces*,
Invent. Math. 129 (1997), p.92: the complexes with coefficients in `ℤ / ℓ ^ n ℤ` "give rise in the
inverse limit over n to a complex of smooth `ℤ_ℓ[S(e,d)]`-modules, whose cohomology equals
`H_c^•(U(e,N), ℤ_ℓ)`. [...] Tensoring with `ℚ_ℓ`, we obtain our complex `C(e,d)`." Deligne,
SGA 4½, *Rapport*, 2.10, p.84, likewise defines the compactly supported cohomology of a
`ℚ_ℓ`-sheaf `F ~ F' ⊗ ℚ_ℓ` as `(lim_n H^q_c(X, F' ⊗ ℤ/ℓ^n)) ⊗_{ℤ_ℓ} ℚ_ℓ`. This module provides, for the `ℓ`-adic limits of the
published `ℓ`-divisible systems and of the truncated smooth Godement section towers, the integral
structure `lim_m H^n`, its extension of scalars, the maps between them, and, for flat algebras such
as `ℤ_[ℓ] → ℚ_[ℓ]`, the comparison of "cohomology, then tensor" with "tensor, then cohomology".
Extension of scalars is Mathlib's `ModuleCat.extendScalars (algebraMap R S)`, or the published
`repExtendScalars` for representations.

* `adicLimitFunctor`, `adicLimitCohomologyFunctor` and `levelCohomologyLimitFunctor`: the
  published `adicLimit`, `H^n(adicLimit K)` and `levelCohomologyLimit K n` as functors of the
  `ℓ`-divisible system `K`, with the published `adicLimitComparison` as a natural transformation
  `adicLimitComparisonNatTrans`.
* `rationalAdicLimitCohomology R S ℓ n`, `rationalLevelCohomologyLimit R S ℓ n` and
  `rationalAdicLimitComparison`: their extensions of scalars `S ⊗_R H^n(lim_m K_m)`,
  `S ⊗_R lim_m H^n(K_m)` and the comparison, an isomorphism given
  `FiniteCohomologyInverseLimitStatement R` and finite level cohomology
  (`isIso_rationalAdicLimitComparison_app`); the units `x ↦ 1 ⊗ x`
  (`adicLimitCohomologyRationalUnit`, `levelCohomologyLimitRationalUnit`) commute with the
  comparisons (`adicLimitComparisonNatTrans_comp_rationalUnit`). The `rep…` declarations are the
  same for systems of complexes of representations.
* `moduleExtendScalars_additive`, `moduleExtendScalars_map_exact` and
  `moduleExtendScalars_preservesHomology`: extension of scalars of modules is additive, and exact
  along a flat algebra. Hence `adicLimitBaseChangeHomologyIso`:
  `H^n(S ⊗_R lim_m K_m) ≅ S ⊗_R H^n(lim_m K_m)` naturally in `K`, and
  `adicLimitBaseChangeLevelCohomologyIso` with target `S ⊗_R lim_m H^n(K_m)`; the
  representation versions use the published `repExtendScalars_preservesHomology`.
* `smoothGodementSectionsCohomologyLimit h T Φ n`: the integral structure `lim_m H^n(Φ(F_m^•))`
  for the smooth Godement resolutions `F_m^•` of the levels of `T`;
  `smoothGodementRationalCohomology` and `smoothGodementRepRationalCohomology` its rational
  structure, with units, the isomorphisms `smoothGodement(Rep)RationalAdicLimitIso` and
  `smoothGodement(Rep)BaseChangeAdicLimitHomologyIso` from the `ℓ`-adic limit of the truncated
  section complexes (`n ≤ D + 1`), and the compatibility of the units with the published integral
  isomorphisms.
* `smoothGodementQuotientInvariantsInverseLimitBaseChangeHomologyIso`: Harris 1999, Lemma 2.8,
  after a flat extension of scalars: `H^n((lim C_m^•) ⊗_R S) ≅ S ⊗_R lim_m H^n(Γ_c(F_m^•))` for
  `n ≤ D + 1`.
* `padicInt_flat_padic`: `ℚ_[ℓ]` is flat over `ℤ_[ℓ]`. `padicConstantGodementRationalCohomology`,
  `padicConstantGodementBaseChangeAdicLimitHomologyIso`,
  `padicConstantQuotientInvariantsInverseLimitRational` and
  `padicConstantQuotientInvariantsInverseLimitRationalHomologyIso` are the cases of the constant
  systems `{ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ]}` with `S = ℚ_[ℓ]`.

The exactness of the degree-zero smooth Godement functor, the surjectivity hypotheses on the
sections functors and invariants, `FiniteCohomologyInverseLimitStatement`,
`ProPInvariantSubcomplexStatement`, finiteness of the level cohomology and triviality of the
actions on it remain explicit hypotheses. Smoothness of the limits and the `ℓ`-adic sheaf `W̃`
are not formalized.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

open scoped ChangeOfRings TensorProduct

universe w v u v' u' uS

namespace DivisibleSystem

section AdicLimitFunctor

variable (E : Type u') [Category.{v'} E] [Abelian E] [HasLimitsOfShape ℕᵒᵖ E] (ℓ : ℕ)

/-- The `ℓ`-adic limit `K ↦ lim_m K_m` (levels extended by zero to `ℤ`) as a functor on
`ℓ`-divisible systems of `ℕ`-graded complexes. -/
def adicLimitFunctor : DivisibleSystem (CochainComplex E ℕ) ℓ ⥤ CochainComplex E ℤ :=
  mapFunctor (CochainComplex E ℕ) ℓ (ComplexShape.embeddingUpNat.extendFunctor E) ⋙
    forget (CochainComplex E ℤ) ℓ ⋙ lim

lemma adicLimitFunctor_obj (K : DivisibleSystem (CochainComplex E ℕ) ℓ) :
    (adicLimitFunctor E ℓ).obj K = K.adicLimit :=
  rfl

/-- `K ↦ H^n(lim_m K_m)`, the integral cohomology of the `ℓ`-adic limit, as a functor. -/
def adicLimitCohomologyFunctor (n : ℕ) : DivisibleSystem (CochainComplex E ℕ) ℓ ⥤ E :=
  adicLimitFunctor E ℓ ⋙ HomologicalComplex.homologyFunctor E (ComplexShape.up ℤ) n

lemma adicLimitCohomologyFunctor_obj (n : ℕ) (K : DivisibleSystem (CochainComplex E ℕ) ℓ) :
    (adicLimitCohomologyFunctor E ℓ n).obj K = K.adicLimit.homology n :=
  rfl

/-- `K ↦ lim_m H^n(K_m)`, as a functor. -/
def levelCohomologyLimitFunctor (n : ℕ) : DivisibleSystem (CochainComplex E ℕ) ℓ ⥤ E :=
  forget (CochainComplex E ℕ) ℓ ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) ⋙ lim

lemma levelCohomologyLimitFunctor_obj (n : ℕ) (K : DivisibleSystem (CochainComplex E ℕ) ℓ) :
    (levelCohomologyLimitFunctor E ℓ n).obj K = K.levelCohomologyLimit n :=
  rfl

/-- `adicLimitComparison`, natural in the `ℓ`-divisible system. -/
def adicLimitComparisonNatTrans (n : ℕ) :
    adicLimitCohomologyFunctor E ℓ n ⟶ levelCohomologyLimitFunctor E ℓ n where
  app K := K.adicLimitComparison n
  naturality K L f := by
    refine limit.hom_ext fun m => ?_
    have h₁ : limMap (Functor.whiskerRight f.tower (ComplexShape.embeddingUpNat.extendFunctor E)) ≫
        limit.π L.extendSystem.tower m =
          limit.π K.extendSystem.tower m ≫
            (ComplexShape.embeddingUpNat.extendFunctor E).map (f.tower.app m) :=
      limMap_π _ _
    have h₂ : limMap (Functor.whiskerRight f.tower
          (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n)) ≫
        limit.π (L.tower ⋙ HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) m =
          limit.π (K.tower ⋙ HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) m ≫
            (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map (f.tower.app m) :=
      limMap_π _ _
    have h₃ := (extendHomologyNatIso E n).hom.naturality (f.tower.app m)
    erw [Category.assoc, adicLimitComparison_π, Category.assoc, h₂, adicLimitComparison_π_assoc,
      ← (HomologicalComplex.homologyFunctor E (ComplexShape.up ℤ) n).map_comp_assoc, h₁,
      Functor.map_comp_assoc]
    exact (congrArg ((HomologicalComplex.homologyFunctor E (ComplexShape.up ℤ) n).map
      (limit.π K.extendSystem.tower m) ≫ ·) h₃).trans (Category.assoc _ _ _).symm

@[simp]
lemma adicLimitComparisonNatTrans_app (n : ℕ) (K : DivisibleSystem (CochainComplex E ℕ) ℓ) :
    (adicLimitComparisonNatTrans E ℓ n).app K = K.adicLimitComparison n :=
  rfl

end AdicLimitFunctor

section RationalModules

variable (R : Type u) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S] (ℓ : ℕ)

/-- `K ↦ S ⊗_R H^n(lim_m K_m)`: extension of scalars of `adicLimitCohomologyFunctor`. -/
def rationalAdicLimitCohomology (n : ℕ) :
    DivisibleSystem (CochainComplex (ModuleCat.{v} R) ℕ) ℓ ⥤ ModuleCat.{max v uS} S :=
  adicLimitCohomologyFunctor (ModuleCat.{v} R) ℓ n ⋙ ModuleCat.extendScalars (algebraMap R S)

/-- `K ↦ S ⊗_R lim_m H^n(K_m)`: extension of scalars of `levelCohomologyLimitFunctor`. -/
def rationalLevelCohomologyLimit (n : ℕ) :
    DivisibleSystem (CochainComplex (ModuleCat.{v} R) ℕ) ℓ ⥤ ModuleCat.{max v uS} S :=
  levelCohomologyLimitFunctor (ModuleCat.{v} R) ℓ n ⋙ ModuleCat.extendScalars (algebraMap R S)

/-- The comparison `S ⊗_R H^n(lim_m K_m) ⟶ S ⊗_R lim_m H^n(K_m)`. -/
def rationalAdicLimitComparison (n : ℕ) :
    rationalAdicLimitCohomology.{v} R S ℓ n ⟶ rationalLevelCohomologyLimit.{v} R S ℓ n :=
  Functor.whiskerRight (adicLimitComparisonNatTrans (ModuleCat.{v} R) ℓ n) _

lemma rationalAdicLimitComparison_app (n : ℕ)
    (K : DivisibleSystem (CochainComplex (ModuleCat.{v} R) ℕ) ℓ) :
    (rationalAdicLimitComparison.{v} R S ℓ n).app K =
      (ModuleCat.extendScalars (algebraMap R S)).map (K.adicLimitComparison n) :=
  rfl

/-- Given `FiniteCohomologyInverseLimitStatement` and finite cohomology of the levels, the
rational comparison is an isomorphism. -/
theorem isIso_rationalAdicLimitComparison_app (hS : FiniteCohomologyInverseLimitStatement.{u, v} R)
    (K : DivisibleSystem (CochainComplex (ModuleCat.{v} R) ℕ) ℓ)
    (hfin : ∀ m n, Finite ((K.obj m).homology n)) (n : ℕ) :
    IsIso ((rationalAdicLimitComparison.{v} R S ℓ n).app K) := by
  have := isIso_adicLimitComparison_of_finite hS K hfin n
  exact (ModuleCat.extendScalars (algebraMap R S)).map_isIso (K.adicLimitComparison n)

/-- The map `x ↦ 1 ⊗ x` from `H^n(lim_m K_m)` to its extension of scalars. -/
def adicLimitCohomologyRationalUnit (n : ℕ) :
    adicLimitCohomologyFunctor (ModuleCat.{max v uS} R) ℓ n ⟶
      rationalAdicLimitCohomology.{max v uS} R S ℓ n ⋙ ModuleCat.restrictScalars (algebraMap R S) where
  app _ := (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app _
  naturality _ _ _ := (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.naturality _

/-- The map `x ↦ 1 ⊗ x` from `lim_m H^n(K_m)` to its extension of scalars. -/
def levelCohomologyLimitRationalUnit (n : ℕ) :
    levelCohomologyLimitFunctor (ModuleCat.{max v uS} R) ℓ n ⟶
      rationalLevelCohomologyLimit.{max v uS} R S ℓ n ⋙ ModuleCat.restrictScalars (algebraMap R S) where
  app _ := (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app _
  naturality _ _ _ := (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.naturality _

lemma adicLimitCohomologyRationalUnit_app_apply (n : ℕ)
    (K : DivisibleSystem (CochainComplex (ModuleCat.{max v uS} R) ℕ) ℓ)
    (x : K.adicLimit.homology n) :
    (adicLimitCohomologyRationalUnit.{v} R S ℓ n).app K x = (1 : S) ⊗ₜ[R, algebraMap R S] x :=
  rfl

lemma levelCohomologyLimitRationalUnit_app_apply (n : ℕ)
    (K : DivisibleSystem (CochainComplex (ModuleCat.{max v uS} R) ℕ) ℓ)
    (x : K.levelCohomologyLimit n) :
    (levelCohomologyLimitRationalUnit.{v} R S ℓ n).app K x = (1 : S) ⊗ₜ[R, algebraMap R S] x :=
  rfl

/-- The integral and rational comparisons are compatible with the maps `x ↦ 1 ⊗ x`. -/
lemma adicLimitComparisonNatTrans_comp_rationalUnit (n : ℕ) :
    adicLimitComparisonNatTrans (ModuleCat.{max v uS} R) ℓ n ≫
        levelCohomologyLimitRationalUnit.{v} R S ℓ n =
      adicLimitCohomologyRationalUnit.{v} R S ℓ n ≫
        Functor.whiskerRight (rationalAdicLimitComparison.{max v uS} R S ℓ n)
          (ModuleCat.restrictScalars (algebraMap R S)) :=
  NatTrans.ext (funext fun K =>
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.naturality (K.adicLimitComparison n))

end RationalModules

section ExtendScalarsAdditive

/-- Extension of scalars of modules, in any universe of modules, is additive. -/
instance moduleExtendScalars_additive {R : Type u} [CommRing R] {S : Type uS} [CommRing S]
    (φ : R →+* S) : (ModuleCat.extendScalars.{u, uS, v} φ).Additive where
  map_add {_ _ f g} := by
    let := φ.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change (1 : S) ⊗ₜ[R, φ] (f.hom m + g.hom m) =
      (1 : S) ⊗ₜ[R, φ] f.hom m + (1 : S) ⊗ₜ[R, φ] g.hom m
    exact TensorProduct.tmul_add _ _ _

end ExtendScalarsAdditive

section FlatModules

variable (R : Type u) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]

/-- Extension of scalars along a flat algebra `R → S` sends exact short complexes of modules to
exact short complexes. -/
theorem moduleExtendScalars_map_exact [Module.Flat R S] (T : ShortComplex (ModuleCat.{v} R))
    (hT : T.Exact) : (T.map (ModuleCat.extendScalars (algebraMap R S))).Exact := by
  have hf : ((algebraMap S S).comp (algebraMap R S)).Flat := by
    rw [Algebra.algebraMap_self, RingHom.id_comp]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker, eq_comm, ← LinearMap.exact_iff] at hT ⊢
  let := ((algebraMap S S).comp (algebraMap R S)).toAlgebra
  have : Module.Flat R S := hf
  exact Module.Flat.lTensor_exact S hT

instance moduleExtendScalars_preservesHomology [Module.Flat R S] :
    (ModuleCat.extendScalars.{u, uS, v} (algebraMap R S)).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (moduleExtendScalars_map_exact.{v} R S)

variable (ℓ : ℕ)

/-- For a flat algebra `R → S`, the cohomology of the degreewise extension of scalars of the
`ℓ`-adic limit is the extension of scalars of its cohomology:
`H^n(S ⊗_R lim_m K_m) ≅ S ⊗_R H^n(lim_m K_m)`, naturally in `K`. -/
def adicLimitBaseChangeHomologyIso [Module.Flat R S] (n : ℕ) :
    adicLimitFunctor (ModuleCat.{v} R) ℓ ⋙
        (ModuleCat.extendScalars.{u, uS, v} (algebraMap R S)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n ≅
      rationalAdicLimitCohomology.{v} R S ℓ n :=
  Functor.isoWhiskerLeft (adicLimitFunctor (ModuleCat.{v} R) ℓ)
      (mapHomologicalComplexHomologyIso (ModuleCat.extendScalars.{u, uS, v} (algebraMap R S))
        (ComplexShape.up ℤ) (n : ℤ)) ≪≫
    (Functor.associator _ _ _).symm

/-- For a flat algebra `R → S`, given `FiniteCohomologyInverseLimitStatement` and finite
cohomology of the levels, `H^n(S ⊗_R lim_m K_m) ≅ S ⊗_R lim_m H^n(K_m)`. -/
def adicLimitBaseChangeLevelCohomologyIso [Module.Flat R S]
    (hS : FiniteCohomologyInverseLimitStatement.{u, v} R)
    (K : DivisibleSystem (CochainComplex (ModuleCat.{v} R) ℕ) ℓ)
    (hfin : ∀ m n, Finite ((K.obj m).homology n)) (n : ℕ) :
    (((ModuleCat.extendScalars.{u, uS, v} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K.adicLimit).homology n ≅
      (rationalLevelCohomologyLimit.{v} R S ℓ n).obj K :=
  haveI := isIso_rationalAdicLimitComparison_app R S ℓ hS K hfin n
  (adicLimitBaseChangeHomologyIso.{v} R S ℓ n).app K ≪≫
    asIso ((rationalAdicLimitComparison.{v} R S ℓ n).app K)

end FlatModules

section RationalRep

variable (k : Type u) [CommRing k] (S : Type uS) [CommRing S] [Algebra k S] (G : Type w)
  [Monoid G] (ℓ : ℕ)

/-- `K ↦ S ⊗_k H^n(lim_m K_m)` for systems of complexes of representations of `G` over `k`. -/
def repRationalAdicLimitCohomology (n : ℕ) :
    DivisibleSystem (CochainComplex (Rep.{v} k G) ℕ) ℓ ⥤ Rep.{max uS v} S G :=
  adicLimitCohomologyFunctor (Rep.{v} k G) ℓ n ⋙ repExtendScalars k S G

/-- `K ↦ S ⊗_k lim_m H^n(K_m)` for systems of complexes of representations of `G` over `k`. -/
def repRationalLevelCohomologyLimit (n : ℕ) :
    DivisibleSystem (CochainComplex (Rep.{v} k G) ℕ) ℓ ⥤ Rep.{max uS v} S G :=
  levelCohomologyLimitFunctor (Rep.{v} k G) ℓ n ⋙ repExtendScalars k S G

/-- The comparison `S ⊗_k H^n(lim_m K_m) ⟶ S ⊗_k lim_m H^n(K_m)` of representations. -/
def repRationalAdicLimitComparison (n : ℕ) :
    repRationalAdicLimitCohomology.{w, v} k S G ℓ n ⟶
      repRationalLevelCohomologyLimit.{w, v} k S G ℓ n :=
  Functor.whiskerRight (adicLimitComparisonNatTrans (Rep.{v} k G) ℓ n) _

lemma repRationalAdicLimitComparison_app (n : ℕ)
    (K : DivisibleSystem (CochainComplex (Rep.{v} k G) ℕ) ℓ) :
    (repRationalAdicLimitComparison.{w, v} k S G ℓ n).app K =
      (repExtendScalars k S G).map (K.adicLimitComparison n) :=
  rfl

/-- Given `FiniteCohomologyInverseLimitStatement` for `k` and finite cohomology of the levels,
the comparison of representations is an isomorphism. -/
theorem isIso_repRationalAdicLimitComparison_app
    (hS : FiniteCohomologyInverseLimitStatement.{u, v} k)
    (K : DivisibleSystem (CochainComplex (Rep.{v} k G) ℕ) ℓ)
    (hfin : ∀ m n, Finite ((K.obj m).homology n)) (n : ℕ) :
    IsIso ((repRationalAdicLimitComparison.{w, v} k S G ℓ n).app K) := by
  have := isIso_adicLimitComparison_rep hS K hfin n
  exact (repExtendScalars k S G).map_isIso (K.adicLimitComparison n)

/-- The map `v ↦ 1 ⊗ v` from `H^n(lim_m K_m)` to its extension of scalars. -/
def repAdicLimitCohomologyRationalUnit (n : ℕ) :
    adicLimitCohomologyFunctor (Rep.{max uS v} k G) ℓ n ⟶
      repRationalAdicLimitCohomology.{w, max uS v} k S G ℓ n ⋙ repRestrictScalars k S G where
  app _ := (repExtendScalarsUnit k S G).app _
  naturality _ _ _ := (repExtendScalarsUnit k S G).naturality _

/-- The map `v ↦ 1 ⊗ v` from `lim_m H^n(K_m)` to its extension of scalars. -/
def repLevelCohomologyLimitRationalUnit (n : ℕ) :
    levelCohomologyLimitFunctor (Rep.{max uS v} k G) ℓ n ⟶
      repRationalLevelCohomologyLimit.{w, max uS v} k S G ℓ n ⋙ repRestrictScalars k S G where
  app _ := (repExtendScalarsUnit k S G).app _
  naturality _ _ _ := (repExtendScalarsUnit k S G).naturality _

/-- The integral and rational comparisons of representations are compatible with the maps
`v ↦ 1 ⊗ v`. -/
lemma repAdicLimitComparisonNatTrans_comp_rationalUnit (n : ℕ) :
    adicLimitComparisonNatTrans (Rep.{max uS v} k G) ℓ n ≫
        repLevelCohomologyLimitRationalUnit.{w, v} k S G ℓ n =
      repAdicLimitCohomologyRationalUnit.{w, v} k S G ℓ n ≫
        Functor.whiskerRight (repRationalAdicLimitComparison.{w, max uS v} k S G ℓ n)
          (repRestrictScalars k S G) :=
  NatTrans.ext (funext fun K =>
    (repExtendScalarsUnit k S G).naturality (K.adicLimitComparison n))

/-- For a flat algebra `k → S`, `H^n(S ⊗_k lim_m K_m) ≅ S ⊗_k H^n(lim_m K_m)` for systems of
complexes of representations, naturally in `K`. -/
def repAdicLimitBaseChangeHomologyIso [Module.Flat k S] (n : ℕ) :
    adicLimitFunctor (Rep.{v} k G) ℓ ⋙
        (repExtendScalars k S G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n ≅
      repRationalAdicLimitCohomology.{w, v} k S G ℓ n :=
  Functor.isoWhiskerLeft (adicLimitFunctor (Rep.{v} k G) ℓ)
      (mapHomologicalComplexHomologyIso (repExtendScalars.{v} k S G) (ComplexShape.up ℤ)
        (n : ℤ)) ≪≫
    (Functor.associator _ _ _).symm

/-- For a flat algebra `k → S`, given `FiniteCohomologyInverseLimitStatement` and finite
cohomology of the levels, `H^n(S ⊗_k lim_m K_m) ≅ S ⊗_k lim_m H^n(K_m)` for systems of complexes
of representations. -/
def repAdicLimitBaseChangeLevelCohomologyIso [Module.Flat k S]
    (hS : FiniteCohomologyInverseLimitStatement.{u, v} k)
    (K : DivisibleSystem (CochainComplex (Rep.{v} k G) ℕ) ℓ)
    (hfin : ∀ m n, Finite ((K.obj m).homology n)) (n : ℕ) :
    (((repExtendScalars k S G).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K.adicLimit).homology n ≅
      (repRationalLevelCohomologyLimit.{w, v} k S G ℓ n).obj K :=
  haveI := isIso_repRationalAdicLimitComparison_app k S G ℓ hS K hfin n
  (repAdicLimitBaseChangeHomologyIso.{w, v} k S G ℓ n).app K ≪≫
    asIso ((repRationalAdicLimitComparison.{w, v} k S G ℓ n).app K)

end RationalRep

section SmoothGodementRational

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)

/-- The integral structure `lim_m H^n(Φ(F_m^•))`: the inverse limit over `m` of the degree-`n`
cohomologies of the section complexes of the smooth Godement resolutions of the levels of `T`. -/
abbrev smoothGodementSectionsCohomologyLimit {E : Type u'} [Category.{v'} E] [Abelian E]
    [HasLimitsOfShape ℕᵒᵖ E] (Φ : SmoothTopologicalSheaf R G X ⥤ E) [Φ.Additive]
    [PreservesFiniteLimits Φ] (n : ℕ) : E :=
  limit (smoothGodementSectionsTower h T Φ ⋙
    HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n)

variable {R' : Type u'} [CommRing R'] (S : Type uS) [CommRing S] [Algebra R' S]

/-- The rational structure `S ⊗_{R'} lim_m H^n(Φ(F_m^•))`, for a sections functor `Φ` with values
in `R'`-modules. -/
abbrev smoothGodementRationalCohomology (Φ : SmoothTopologicalSheaf R G X ⥤ ModuleCat.{v'} R')
    [Φ.Additive] [PreservesFiniteLimits Φ] (n : ℕ) : ModuleCat.{max v' uS} S :=
  (ModuleCat.extendScalars (algebraMap R' S)).obj (smoothGodementSectionsCohomologyLimit h T Φ n)

/-- The map `x ↦ 1 ⊗ x` from the integral structure `lim_m H^n(Φ(F_m^•))` to the rational
structure. -/
def smoothGodementRationalCohomologyUnit
    (Φ : SmoothTopologicalSheaf R G X ⥤ ModuleCat.{max v' uS} R') [Φ.Additive]
    [PreservesFiniteLimits Φ] (n : ℕ) :
    smoothGodementSectionsCohomologyLimit h T Φ n ⟶
      (ModuleCat.restrictScalars (algebraMap R' S)).obj
        (smoothGodementRationalCohomology h T S Φ n) :=
  (ModuleCat.extendRestrictScalarsAdj (algebraMap R' S)).unit.app _

lemma smoothGodementRationalCohomologyUnit_apply
    (Φ : SmoothTopologicalSheaf R G X ⥤ ModuleCat.{max v' uS} R') [Φ.Additive]
    [PreservesFiniteLimits Φ] (n : ℕ)
    (x : (smoothGodementSectionsCohomologyLimit h T Φ n : ModuleCat.{max v' uS} R')) :
    smoothGodementRationalCohomologyUnit h T S Φ n x = (1 : S) ⊗ₜ[R', algebraMap R' S] x :=
  rfl

variable (D : ℕ)

/-- Given `FiniteCohomologyInverseLimitStatement` and finite cohomology of the truncated section
complexes, for `n ≤ D + 1` the extension of scalars of the degree-`n` cohomology of the `ℓ`-adic
limit of the truncated section complexes is the rational structure:
`S ⊗_{R'} H^n(lim_m G_m^•) ≅ S ⊗_{R'} lim_m H^n(Φ(F_m^•))`. -/
def smoothGodementRationalAdicLimitIso
    (Φ : SmoothTopologicalSheaf R G X ⥤ ModuleCat.{v'} R') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{u', v'} R')
    (hfin : ∀ m n, Finite
      (((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (rationalAdicLimitCohomology R' S ℓ n).obj
        (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres) ≅
      smoothGodementRationalCohomology h T S Φ n :=
  (ModuleCat.extendScalars (algebraMap R' S)).mapIso
    (smoothGodementTruncatedSectionsAdicLimitHomologyIso h T D Φ hterm hres hS hfin hn)

/-- The integral and rational limit isomorphisms are compatible with the maps `x ↦ 1 ⊗ x`. -/
lemma smoothGodementTruncatedSectionsAdicLimitHomologyIso_hom_comp_rationalUnit
    (Φ : SmoothTopologicalSheaf R G X ⥤ ModuleCat.{max v' uS} R') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{u', max v' uS} R')
    (hfin : ∀ m n, Finite
      (((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (smoothGodementTruncatedSectionsAdicLimitHomologyIso h T D Φ hterm hres hS hfin hn).hom ≫
        smoothGodementRationalCohomologyUnit h T S Φ n =
      (adicLimitCohomologyRationalUnit R' S ℓ n).app
          (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres) ≫
        (ModuleCat.restrictScalars (algebraMap R' S)).map
          (smoothGodementRationalAdicLimitIso h T S D Φ hterm hres hS hfin hn).hom :=
  (ModuleCat.extendRestrictScalarsAdj (algebraMap R' S)).unit.naturality _

/-- For a flat algebra `R' → S`, under the hypotheses of `smoothGodementRationalAdicLimitIso`,
the degree-`n` cohomology of the degreewise extension of scalars of the `ℓ`-adic limit of the
truncated section complexes is the rational structure:
`H^n(S ⊗_{R'} lim_m G_m^•) ≅ S ⊗_{R'} lim_m H^n(Φ(F_m^•))` for `n ≤ D + 1`. -/
def smoothGodementBaseChangeAdicLimitHomologyIso [Module.Flat R' S]
    (Φ : SmoothTopologicalSheaf R G X ⥤ ModuleCat.{v'} R') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{u', v'} R')
    (hfin : ∀ m n, Finite
      (((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (((ModuleCat.extendScalars.{u', uS, v'} (algebraMap R' S)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).adicLimit).homology n ≅
      smoothGodementRationalCohomology h T S Φ n :=
  (adicLimitBaseChangeHomologyIso R' S ℓ n).app _ ≪≫
    smoothGodementRationalAdicLimitIso h T S D Φ hterm hres hS hfin hn

end SmoothGodementRational

section SmoothGodementRationalRep

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  {k : Type u'} [CommRing k] (S : Type uS) [CommRing S] [Algebra k S] {G' : Type w} [Monoid G']

/-- The rational structure `S ⊗_k lim_m H^n(Φ(F_m^•))`, for a sections functor `Φ` with values in
representations of `G'` over `k`. -/
abbrev smoothGodementRepRationalCohomology (Φ : SmoothTopologicalSheaf R G X ⥤ Rep.{v'} k G')
    [Φ.Additive] [PreservesFiniteLimits Φ] (n : ℕ) : Rep.{max uS v'} S G' :=
  (repExtendScalars k S G').obj (smoothGodementSectionsCohomologyLimit h T Φ n)

/-- The map `v ↦ 1 ⊗ v` from the integral structure `lim_m H^n(Φ(F_m^•))` to the rational
structure, for representations. -/
def smoothGodementRepRationalCohomologyUnit
    (Φ : SmoothTopologicalSheaf R G X ⥤ Rep.{max uS v'} k G') [Φ.Additive]
    [PreservesFiniteLimits Φ] (n : ℕ) :
    smoothGodementSectionsCohomologyLimit h T Φ n ⟶
      (repRestrictScalars k S G').obj (smoothGodementRepRationalCohomology h T S Φ n) :=
  (repExtendScalarsUnit k S G').app _

variable (D : ℕ)

/-- The representation version of `smoothGodementRationalAdicLimitIso`:
`S ⊗_k H^n(lim_m G_m^•) ≅ S ⊗_k lim_m H^n(Φ(F_m^•))` for `n ≤ D + 1`. -/
def smoothGodementRepRationalAdicLimitIso
    (Φ : SmoothTopologicalSheaf R G X ⥤ Rep.{v'} k G') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{u', v'} k)
    (hfin : ∀ m n, Finite
      (((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (repRationalAdicLimitCohomology k S G' ℓ n).obj
        (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres) ≅
      smoothGodementRepRationalCohomology h T S Φ n :=
  (repExtendScalars k S G').mapIso
    (smoothGodementTruncatedSectionsAdicLimitHomologyIsoRep h T D Φ hterm hres hS hfin hn)

/-- The integral and rational limit isomorphisms of representations are compatible with the
maps `v ↦ 1 ⊗ v`. -/
lemma smoothGodementTruncatedSectionsAdicLimitHomologyIsoRep_hom_comp_rationalUnit
    (Φ : SmoothTopologicalSheaf R G X ⥤ Rep.{max uS v'} k G') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{u', max uS v'} k)
    (hfin : ∀ m n, Finite
      (((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (smoothGodementTruncatedSectionsAdicLimitHomologyIsoRep h T D Φ hterm hres hS hfin hn).hom ≫
        smoothGodementRepRationalCohomologyUnit h T S Φ n =
      (repAdicLimitCohomologyRationalUnit k S G' ℓ n).app
          (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres) ≫
        (repRestrictScalars k S G').map
          (smoothGodementRepRationalAdicLimitIso h T S D Φ hterm hres hS hfin hn).hom :=
  (repExtendScalarsUnit k S G').naturality _

/-- The representation version of `smoothGodementBaseChangeAdicLimitHomologyIso`: for a flat
algebra `k → S`, `H^n(S ⊗_k lim_m G_m^•) ≅ S ⊗_k lim_m H^n(Φ(F_m^•))` for `n ≤ D + 1`. -/
def smoothGodementRepBaseChangeAdicLimitHomologyIso [Module.Flat k S]
    (Φ : SmoothTopologicalSheaf R G X ⥤ Rep.{v'} k G') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{u', v'} k)
    (hfin : ∀ m n, Finite
      (((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (((repExtendScalars k S G').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).adicLimit).homology n ≅
      smoothGodementRepRationalCohomology h T S Φ n :=
  (repAdicLimitBaseChangeHomologyIso k S G' ℓ n).app _ ≪≫
    smoothGodementRepRationalAdicLimitIso h T S D Φ hterm hres hS hfin hn

end SmoothGodementRationalRep

section SmoothGodementRationalLemma28

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ)
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
  (S : Type u) [CommRing S] [Algebra R S]
  {ι : Type u} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H) [∀ i, (H i).Normal]
  [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)] [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (hm : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map
      (((smoothGodementTruncatedCompactSectionsSystem h T D hterm hres).projection hm).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `(lim C_m^•) ⊗ S` for the compact-section complexes of the truncated smooth
Godement resolutions: the published `quotientInvariantsInverseLimitBaseChange` with
`N = D + 2`, the degreewise extension of scalars of `smoothGodementQuotientInvariantsInverseLimit`. -/
abbrev smoothGodementQuotientInvariantsInverseLimitBaseChange : CochainComplex (Rep.{u} S G) ℤ :=
  quotientInvariantsInverseLimitBaseChange.{0, u, u} S (D + 2)
    (smoothGodementTruncatedCompactSectionsSystem h T D hterm hres) H hH hK hk

/-- `smoothGodementQuotientInvariantsInverseLimitBaseChange` is the degreewise extension of
scalars of the published `smoothGodementQuotientInvariantsInverseLimit`. -/
lemma smoothGodementQuotientInvariantsInverseLimitBaseChange_eq :
    smoothGodementQuotientInvariantsInverseLimitBaseChange h T D hterm hres S H hH hK hk =
      (repExtendScalarsComplex.{u} R S G (ComplexShape.up ℤ)).obj
        (smoothGodementQuotientInvariantsInverseLimit h T D hterm hres H hH hK hk) :=
  rfl

/-- Harris's Lemma 2.8 after the flat extension of scalars `R → S` ("tensoring with `ℚ_ℓ`"), in
degrees `n ≤ D + 1`: under the hypotheses of `smoothGodementQuotientInvariantsInverseLimitHomologyIso`,
`H^n((lim C_m^•) ⊗_R S) ≅ S ⊗_R lim_m H^n(Γ_c(F_m^•))` as representations of `G`. -/
def smoothGodementQuotientInvariantsInverseLimitBaseChangeHomologyIso [Module.Flat R S]
    (hS : ProPInvariantSubcomplexStatement.{u, u, u})
    (hS' : FiniteCohomologyInverseLimitStatement.{u, u} R) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : H i), (((smoothGodementTruncatedCompactSectionsSystem h T D hterm
      hres).toRepComplexes.obj m).homology q).ρ g = LinearMap.id)
    (hfin : ∀ m n, Finite (((smoothGodementTruncatedCompactSectionsSystem h T D hterm
      hres).toRepComplexes.obj m).homology n)) {n : ℕ} (hn : n ≤ D + 1) :
    (smoothGodementQuotientInvariantsInverseLimitBaseChange h T D hterm hres S H hH hK
        hk).homology n ≅
      (repExtendScalars R S G).obj (limit (smoothGodementCompactSectionsRepTower h T ⋙
        HomologicalComplex.homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) n)) :=
  (mapHomologicalComplexHomologyIso (repExtendScalars.{u} R S G) (ComplexShape.up ℤ)
      (n : ℤ)).app (smoothGodementQuotientInvariantsInverseLimit h T D hterm hres H hH hK hk) ≪≫
    (repExtendScalars R S G).mapIso
      (smoothGodementQuotientInvariantsInverseLimitHomologyIso h T D hterm hres H hH hK hk hS hS'
        hP hR htriv hfin hn)

end SmoothGodementRationalLemma28

section PadicRational

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `ℚ_[ℓ]` is flat over `ℤ_[ℓ]`, being its fraction field. -/
instance padicInt_flat_padic : Module.Flat ℤ_[ℓ] ℚ_[ℓ] :=
  IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])

end PadicRational

section PadicRationalGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable (ℓ : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : Type) [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]
  (h : SmoothGodementZeroExactStatement ℤ_[ℓ] G X)

/-- The rational `ℓ`-adic cohomology `ℚ_ℓ ⊗_{ℤ_ℓ} lim_m H^n(Φ(F_m^•))` of the constant system
`{ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ]}`, for a sections functor `Φ` with values in `ℤ_[ℓ]`-modules. -/
abbrev padicConstantGodementRationalCohomology
    (Φ : SmoothTopologicalSheaf ℤ_[ℓ] G X ⥤ ModuleCat.{v'} ℤ_[ℓ]) [Φ.Additive]
    [PreservesFiniteLimits Φ] (n : ℕ) : ModuleCat.{v'} ℚ_[ℓ] :=
  smoothGodementRationalCohomology h (constantSheafSystem (padicInt_isSMulRegular ℓ) G X) ℚ_[ℓ]
    Φ n

variable (D : ℕ)

/-- For the constant system `{ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ]}` and `n ≤ D + 1`, under the hypotheses of
`smoothGodementBaseChangeAdicLimitHomologyIso`:
`H^n(ℚ_ℓ ⊗_{ℤ_ℓ} lim_m G_m^•) ≅ ℚ_ℓ ⊗_{ℤ_ℓ} lim_m H^n(Φ(F_m^•))`. -/
def padicConstantGodementBaseChangeAdicLimitHomologyIso
    (Φ : SmoothTopologicalSheaf ℤ_[ℓ] G X ⥤ ModuleCat.{v'} ℤ_[ℓ]) [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (constantSheafSystem (padicInt_isSMulRegular ℓ) G X)
        q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h
        (constantSheafSystem (padicInt_isSMulRegular ℓ) G X) (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{0, v'} ℤ_[ℓ])
    (hfin : ∀ m n, Finite
      (((constantGodementTruncatedSectionsSystem (padicInt_isSMulRegular ℓ) G X h D Φ hterm
        hres).obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (((ModuleCat.extendScalars.{0, 0, v'} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (constantGodementAdicSectionsComplex (padicInt_isSMulRegular ℓ) G X h D Φ hterm
            hres)).homology n ≅
      padicConstantGodementRationalCohomology ℓ G X h Φ n :=
  smoothGodementBaseChangeAdicLimitHomologyIso h _ ℚ_[ℓ] D Φ hterm hres hS hfin hn

variable
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections ℤ_[ℓ] G X).map
      ((smoothGodementTermSystem h (constantSheafSystem (padicInt_isSMulRegular ℓ) G X)
        q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections ℤ_[ℓ] G X).map
      ((smoothGodementResidualSystem h (constantSheafSystem (padicInt_isSMulRegular ℓ) G X)
        (D + 1)).projection hm)))
  {ι : Type} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H) [∀ i, (H i).Normal]
  [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)] [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (hm : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants ℤ_[ℓ] (H i)).map
      (((constantGodementTruncatedCompactSectionsSystem (padicInt_isSMulRegular ℓ) G X h D
        hterm hres).projection hm).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), ℓ.Coprime (Nat.card (quotientProjection (hH hij)).ker))
  [IsFiltered ι]

/-- Harris's `(lim C_m^•) ⊗_{ℤ_ℓ} ℚ_ℓ` for the constant system `{ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ]}`: the
degreewise extension of scalars of the published `padicConstantQuotientInvariantsInverseLimit`. -/
abbrev padicConstantQuotientInvariantsInverseLimitRational :
    CochainComplex (Rep.{0} ℚ_[ℓ] G) ℤ :=
  smoothGodementQuotientInvariantsInverseLimitBaseChange h
    (constantSheafSystem (padicInt_isSMulRegular ℓ) G X) D hterm hres ℚ_[ℓ] H hH hK
    (fun hij => padicInt_isUnit_natCast (hk hij))

/-- `padicConstantQuotientInvariantsInverseLimitRational` is the degreewise extension of scalars
along `ℤ_[ℓ] → ℚ_[ℓ]` of the published `padicConstantQuotientInvariantsInverseLimit`. -/
lemma padicConstantQuotientInvariantsInverseLimitRational_eq :
    padicConstantQuotientInvariantsInverseLimitRational ℓ G X h D hterm hres H hH hK hk =
      (repExtendScalarsComplex.{0} ℤ_[ℓ] ℚ_[ℓ] G (ComplexShape.up ℤ)).obj
        (padicConstantQuotientInvariantsInverseLimit ℓ G X h D hterm hres H hH hK hk) :=
  rfl

/-- Harris's Lemma 2.8 with `ℚ_ℓ` coefficients in degrees `n ≤ D + 1`: for a family of pro-`p`
subgroups with `p` prime to `ℓ`, under the remaining hypotheses of
`padicConstantQuotientInvariantsInverseLimitHomologyIso`,
`H^n((lim C_m^•) ⊗_{ℤ_ℓ} ℚ_ℓ) ≅ ℚ_ℓ ⊗_{ℤ_ℓ} lim_m H^n(Γ_c(F_m^•))`, where `F_m^•` is the smooth
Godement resolution of the constant sheaf of `ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ]`. -/
def padicConstantQuotientInvariantsInverseLimitRationalHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{0, 0, 0})
    (hS' : FiniteCohomologyInverseLimitStatement.{0, 0} ℤ_[ℓ]) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hpℓ : ℓ.Coprime p)
    (htriv : ∀ m i q (g : H i), (((constantGodementTruncatedCompactSectionsSystem
      (padicInt_isSMulRegular ℓ) G X h D hterm hres).toRepComplexes.obj m).homology q).ρ g =
        LinearMap.id)
    (hfin : ∀ m n, Finite (((constantGodementTruncatedCompactSectionsSystem
      (padicInt_isSMulRegular ℓ) G X h D hterm hres).toRepComplexes.obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (padicConstantQuotientInvariantsInverseLimitRational ℓ G X h D hterm hres H hH hK
        hk).homology n ≅
      (repExtendScalars ℤ_[ℓ] ℚ_[ℓ] G).obj (limit (smoothGodementCompactSectionsRepTower h
          (constantSheafSystem (padicInt_isSMulRegular ℓ) G X) ⋙
        HomologicalComplex.homologyFunctor (Rep.{0} ℤ_[ℓ] G) (ComplexShape.up ℕ) n)) :=
  smoothGodementQuotientInvariantsInverseLimitBaseChangeHomologyIso h _ D hterm hres ℚ_[ℓ] H hH
    hK (fun hij => padicInt_isUnit_natCast (hk hij)) hS hS' hP (padicInt_isUnit_natCast hpℓ)
    htriv hfin hn

end PadicRationalGodement

end DivisibleSystem

end Langlands.Cohomology
