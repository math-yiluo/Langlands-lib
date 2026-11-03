import Langlands.Cohomology.DivisibleSystem.ConstantTruncation
import Langlands.Cohomology.DivisibleSystem.InverseLimit
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# `ℓ`-adic limits of the truncated constant Godement section systems

Harris 1999, §2, pp.305–306: the truncated resolutions `G_m^•` of the constant sheaves
`ℤ / ℓ ^ m ℤ` give `ℓ`-divisible systems of finite-length section complexes `G_m^•(U)`, and
Lemma 2.8 identifies the cohomology of `lim C_m^•` with `lim_m H_c^q(U, ℤ / ℓ ^ m ℤ)`.

* `adicLimit K` is the inverse limit over `m` of the levels of an `ℓ`-divisible system `K` of
  `ℕ`-graded complexes, extended by zero to `ℤ`. `levelCohomologyLimit K n` is `lim_m H^n(K_m)`
  and `adicLimitComparison K n` is the canonical map from `H^n(adicLimit K)` to it. Given
  `FiniteCohomologyInverseLimitStatement` and finite cohomology of the levels it is an
  isomorphism, for modules and for representations.
* `map_truncationHom_quasiIsoAt_of_le`: an additive functor `Φ` preserving finite limits,
  applied degreewise to the inclusion of a truncation, gives a quasi-isomorphism in degrees
  `≤ D`, and in degree `D + 1` too when `Φ` maps the top inclusion to a kernel
  (`map_truncationHom_quasiIsoAt_top`, via `quasiIso_of_epi_of_isLimit_kernelFork`). Hence the
  inclusion of the truncated section complexes `Φ(G_m^•)` into the full ones `Φ(F_m^•)` induces
  isomorphisms on `lim_m H^n` for `n ≤ D + 1`
  (`truncatedResolutionSectionsAdicCohomologyIso`,
  `smoothGodementTruncatedSectionsAdicCohomologyIso`).
* `smoothGodementTruncatedSectionsAdicLimitHomologyIso` and its constant cases
  `constantGodementAdicLimitHomologyIso` and `intConstantGodementAdicLimitHomologyIso` give
  `H^n(lim_m G_m^•(U)) ≅ lim_m H^n(Φ(F_m^•))` for `n ≤ D + 1`, where `F_m^•` is the smooth Godement
  resolution of `T m`, of `R / ℓ ^ m R`, or of `ℤ / ℓ ^ m ℤ`.
* `smoothGodementQuotientInvariantsInverseLimitHomologyIso` and its constant cases compose the
  published Lemma 2.8 for the compact-section complexes of the truncated smooth Godement
  resolutions (with `N = D + 2`) with these identifications in degrees `n ≤ D + 1`. Its
  `ℓ`-adic case `padicConstantQuotientInvariantsInverseLimitHomologyIso` takes coefficients
  `ℤ_[ℓ]`, in which a prime `p ≠ ℓ` is a unit and whose levels are the rings `ZMod (ℓ ^ m)`
  (`padicLevelRingEquiv`). There is no case with coefficients `ℤ`: there the unit hypotheses of
  Lemma 2.8 would force `p = 1`.

The exactness of the degree-zero smooth Godement functor, the surjectivity of the sections
functors on the projections, `FiniteCohomologyInverseLimitStatement`,
`ProPInvariantSubcomplexStatement`, and the finiteness of the level cohomology and triviality of
the actions on it are explicit hypotheses.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u v' u'

section ModuleFinite

variable {R : Type u} [Ring R]

/-- Finiteness of the underlying type of a module is invariant under isomorphism. -/
lemma finite_of_moduleCat_iso {X Y : ModuleCat.{v} R} (e : X ≅ Y) (h : Finite X) : Finite Y :=
  Finite.of_equiv _ e.toLinearEquiv.toEquiv

/-- A zero module has finite underlying type. -/
lemma finite_of_moduleCat_isZero {X : ModuleCat.{v} R} (h : IsZero X) : Finite X :=
  have : Subsingleton X := ModuleCat.isZero_iff_subsingleton.1 h
  Finite.of_subsingleton

/-- If an `ℕ`-graded complex of modules has finite cohomology in every degree, so does its
extension by zero to `ℤ`. -/
lemma finite_homology_extend_embeddingUpNat_moduleCat (X : CochainComplex (ModuleCat.{v} R) ℕ)
    (h : ∀ n, Finite (X.homology n)) (q : ℤ) :
    Finite ((X.extend ComplexShape.embeddingUpNat).homology q) := by
  rcases q with n | n
  · exact finite_of_moduleCat_iso
      (X.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).symm (h n)
  · refine finite_of_moduleCat_isZero
      ((X.extend_exactAt ComplexShape.embeddingUpNat _ fun j hj => ?_).isZero_homology)
    simp only [ComplexShape.embeddingUpNat_f] at hj
    omega

end ModuleFinite

section ShortComplexKernel

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A morphism `φ : S₁ ⟶ S₂` of short complexes is a quasi-isomorphism if `φ.τ₁` is an
epimorphism, `S₁.g = 0`, and `φ.τ₂` is, up to an isomorphism `e` of its source, a kernel of
`S₂.g`. -/
lemma quasiIso_of_epi_of_isLimit_kernelFork {S₁ S₂ : ShortComplex C} (φ : S₁ ⟶ S₂) [Epi φ.τ₁]
    (hg : S₁.g = 0) {K : C} {i : K ⟶ S₂.X₂} {w : i ≫ S₂.g = 0}
    (hc : IsLimit (KernelFork.ofι i w)) (e : S₁.X₂ ≅ K) (he : φ.τ₂ = e.hom ≫ i) :
    ShortComplex.QuasiIso φ := by
  have : IsIso S₁.iCycles := S₁.isIso_iCycles hg
  let e' := IsLimit.conePointUniqueUpToIso hc S₂.cyclesIsKernel
  have he' : e'.hom ≫ S₂.iCycles = i :=
    IsLimit.conePointUniqueUpToIso_hom_comp hc S₂.cyclesIsKernel WalkingParallelPair.zero
  have hcyc : ShortComplex.cyclesMap φ = S₁.iCycles ≫ e.hom ≫ e'.hom := by
    rw [← cancel_mono S₂.iCycles, ShortComplex.cyclesMap_i, Category.assoc, Category.assoc, he',
      he]
  have : IsIso (ShortComplex.cyclesMap φ) := by
    rw [hcyc]
    infer_instance
  rw [ShortComplex.quasiIso_iff]
  exact ShortComplex.isIso_homologyMap_of_isIso_cyclesMap_of_epi this inferInstance

end ShortComplexKernel

section TowerHomology

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {J : Type*} [Category J] [HasLimitsOfShape J C]

/-- For a morphism `α` of diagrams of complexes, the induced morphism between the limits of the
degree-`q` homologies. -/
def limitHomologyMap {K L : J ⥤ HomologicalComplex C c} (α : K ⟶ L) (q : ι) :
    limit (K ⋙ HomologicalComplex.homologyFunctor C c q) ⟶
      limit (L ⋙ HomologicalComplex.homologyFunctor C c q) :=
  limMap (Functor.whiskerRight α (HomologicalComplex.homologyFunctor C c q))

/-- Followed by a limit projection, `limitHomologyMap α q` is the map induced on homology by the
component of `α`. -/
@[reassoc (attr := simp)]
lemma limitHomologyMap_π {K L : J ⥤ HomologicalComplex C c} (α : K ⟶ L) (q : ι) (j : J) :
    limitHomologyMap α q ≫ limit.π _ j =
      limit.π _ j ≫ (HomologicalComplex.homologyFunctor C c q).map (α.app j) :=
  limMap_π _ _

/-- If `α` is a quasi-isomorphism in degree `q` at every index, the induced morphism of the
limits of the degree-`q` homologies is an isomorphism. -/
lemma isIso_limitHomologyMap {K L : J ⥤ HomologicalComplex C c} (α : K ⟶ L) (q : ι)
    (hα : ∀ j, QuasiIsoAt (α.app j) q) : IsIso (limitHomologyMap α q) := by
  have : ∀ j, IsIso ((Functor.whiskerRight α (HomologicalComplex.homologyFunctor C c q)).app j) :=
    fun j => by
      have := hα j
      change IsIso (HomologicalComplex.homologyMap (α.app j) q)
      infer_instance
  have : IsIso (Functor.whiskerRight α (HomologicalComplex.homologyFunctor C c q)) :=
    NatIso.isIso_of_isIso_app _
  unfold limitHomologyMap
  infer_instance

/-- The comparison from the homology of a limit to the limit of the homologies is natural in the
diagram. -/
lemma limit_post_comp_limitHomologyMap {K L : J ⥤ HomologicalComplex C c} (α : K ⟶ L)
    (q : ι) :
    limit.post K (HomologicalComplex.homologyFunctor C c q) ≫ limitHomologyMap α q =
      (HomologicalComplex.homologyFunctor C c q).map (limMap α) ≫
        limit.post L (HomologicalComplex.homologyFunctor C c q) := by
  ext j
  simp only [Category.assoc, limitHomologyMap_π, limit.post_π_assoc, limit.post_π,
    ← Functor.map_comp, limMap_π]

end TowerHomology

section ExtendHomology

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The degree-`n` cohomology of the extension by zero to `ℤ` of an `ℕ`-graded cochain complex
is its degree-`n` cohomology, naturally in the complex. -/
def extendHomologyNatIso (n : ℕ) :
    ComplexShape.embeddingUpNat.extendFunctor C ⋙
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) n :=
  NatIso.ofComponents (fun K => K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl)
    (fun φ => HomologicalComplex.extendHomologyIso_hom_naturality φ ComplexShape.embeddingUpNat
      rfl)

/-- The components of `extendHomologyNatIso` are Mathlib's `extendHomologyIso`. -/
lemma extendHomologyNatIso_hom_app (n : ℕ) (K : CochainComplex C ℕ) :
    (extendHomologyNatIso C n).hom.app K =
      (K.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom :=
  rfl

end ExtendHomology

namespace DivisibleSystem

section AdicLimit

variable {E : Type u'} [Category.{v'} E] [Abelian E] [HasLimitsOfShape ℕᵒᵖ E] {ℓ : ℕ}
  (K : DivisibleSystem (CochainComplex E ℕ) ℓ)

/-- The `ℓ`-adic limit of a system of `ℕ`-graded complexes: the inverse limit over `m` of its
levels extended by zero to `ℤ`. -/
abbrev adicLimit : CochainComplex E ℤ := K.extendSystem.inverseLimit

/-- The inverse limit over `m` of the degree-`n` cohomologies of the levels. -/
abbrev levelCohomologyLimit (n : ℕ) : E :=
  limit (K.tower ⋙ HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n)

/-- The inverse limit over `m` of the degree-`n` cohomologies of the extended levels is that of
the levels themselves. -/
def extendLevelCohomologyLimitIso (n : ℕ) :
    limit (K.extendSystem.tower ⋙ HomologicalComplex.homologyFunctor E (ComplexShape.up ℤ) n) ≅
      K.levelCohomologyLimit n :=
  lim.mapIso (Functor.isoWhiskerLeft K.tower (extendHomologyNatIso E n))

/-- Followed by a limit projection, `extendLevelCohomologyLimitIso` is the component of
`extendHomologyNatIso`. -/
@[reassoc (attr := simp)]
lemma extendLevelCohomologyLimitIso_hom_π (n : ℕ) (m : ℕᵒᵖ) :
    (K.extendLevelCohomologyLimitIso n).hom ≫ limit.π _ m =
      limit.π _ m ≫ (extendHomologyNatIso E n).hom.app (K.tower.obj m) :=
  limMap_π _ _

/-- The comparison from the degree-`n` cohomology of the `ℓ`-adic limit to the inverse limit of
the degree-`n` cohomologies of the levels. -/
def adicLimitComparison (n : ℕ) : K.adicLimit.homology n ⟶ K.levelCohomologyLimit n :=
  K.extendSystem.inverseLimitHomologyComparison n ≫ (K.extendLevelCohomologyLimitIso n).hom

/-- Followed by the projection to level `m`, `adicLimitComparison` is the map induced on
cohomology by the limit projection, followed by the identification of the cohomology of the
extended level. -/
@[reassoc (attr := simp)]
lemma adicLimitComparison_π (n : ℕ) (m : ℕᵒᵖ) :
    K.adicLimitComparison n ≫ limit.π _ m =
      (HomologicalComplex.homologyFunctor E (ComplexShape.up ℤ) n).map
          (limit.π K.extendSystem.tower m) ≫
        (extendHomologyNatIso E n).hom.app (K.tower.obj m) := by
  rw [adicLimitComparison, Category.assoc, extendLevelCohomologyLimitIso_hom_π]
  erw [inverseLimitHomologyComparison_π_assoc]
  rfl

end AdicLimit

section AdicLimitModules

variable {R : Type u} [Ring R] {ℓ : ℕ}

/-- Given `FiniteCohomologyInverseLimitStatement`, for an `ℓ`-divisible system of `ℕ`-graded
complexes of `R`-modules with finite cohomology, the comparison `adicLimitComparison` is an
isomorphism in every degree. -/
theorem isIso_adicLimitComparison_of_finite
    (hS : FiniteCohomologyInverseLimitStatement.{u, v} R)
    (K : DivisibleSystem (CochainComplex (ModuleCat.{v} R) ℕ) ℓ)
    (hfin : ∀ m n, Finite ((K.obj m).homology n)) (n : ℕ) :
    IsIso (K.adicLimitComparison n) := by
  have := isIso_inverseLimitHomologyComparison_of_finite hS K.extendSystem
    (fun m q => finite_homology_extend_embeddingUpNat_moduleCat (K.obj m) (hfin m) q) n
  unfold adicLimitComparison
  infer_instance

end AdicLimitModules

section AdicLimitRep

variable {k : Type u} [CommRing k] {G : Type v} [Monoid G] {ℓ : ℕ}

/-- Given `FiniteCohomologyInverseLimitStatement` for the coefficient ring, for an
`ℓ`-divisible system of `ℕ`-graded complexes of representations with finite cohomology, the
comparison `adicLimitComparison` is an isomorphism in every degree. -/
theorem isIso_adicLimitComparison_rep
    (hS : FiniteCohomologyInverseLimitStatement.{u, w} k)
    (K : DivisibleSystem (CochainComplex (Rep.{w} k G) ℕ) ℓ)
    (hfin : ∀ m n, Finite ((K.obj m).homology n)) (n : ℕ) :
    IsIso (K.adicLimitComparison n) := by
  have := isIso_inverseLimitHomologyComparison_rep hS K.extendSystem
    (fun m q => finite_homology_extend_embeddingUpNat (K.obj m) (hfin m) q) n
  unfold adicLimitComparison
  infer_instance

end AdicLimitRep

section TruncationSections

variable {C : Type u} [Category.{v} C] [Abelian C] {E : Type u'} [Category.{v'} E] [Abelian E]
  {ℓ : ℕ} (S : ℕ → DivisibleSystem C ℓ) (d : ∀ q, S q ⟶ S (q + 1))
  (sq : ∀ q m, (d q).tower.app m ≫ (d (q + 1)).tower.app m = 0)
  (D : ℕ) (Z : DivisibleSystem C ℓ) (p : S D ⟶ Z) (ι : Z ⟶ S (D + 1))
  [∀ m, Mono (ι.tower.app m)] (hpι : ∀ m, p.tower.app m ≫ ι.tower.app m = (d D).tower.app m)
  (hιd : ∀ m, ι.tower.app m ≫ (d (D + 1)).tower.app m = 0)
  (Φ : C ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]

private lemma prev_nat_le (q : ℕ) : (ComplexShape.up ℕ).prev q ≤ q := by
  rcases q with _ | q
  · rw [CochainComplex.prev_nat_zero]
  · rw [CochainComplex.prev_nat_succ]
    omega

/-- At every level, `Φ` applied degreewise to the inclusion of the truncation is a
quasi-isomorphism in degrees `≤ D`. -/
lemma map_truncationHom_quasiIsoAt_of_le (m : ℕ) {q : ℕ} (hq : q ≤ D) :
    QuasiIsoAt ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m))) q := by
  rw [quasiIsoAt_iff]
  have := isIso_truncationInclusion_tower_app S D Z ι ((prev_nat_le q).trans hq) (op m)
  have := isIso_truncationInclusion_tower_app S D Z ι hq (op m)
  have : Epi ((HomologicalComplex.shortComplexFunctor E (ComplexShape.up ℕ) q).map
      ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m)))).τ₁ :=
    show Epi (Φ.map ((truncationInclusion S D Z ι _).tower.app (op m))) from inferInstance
  have : IsIso ((HomologicalComplex.shortComplexFunctor E (ComplexShape.up ℕ) q).map
      ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m)))).τ₂ :=
    show IsIso (Φ.map ((truncationInclusion S D Z ι q).tower.app (op m))) from inferInstance
  have : Mono ((HomologicalComplex.shortComplexFunctor E (ComplexShape.up ℕ) q).map
      ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m)))).τ₃ :=
    show Mono (Φ.map ((truncationInclusion S D Z ι _).tower.app (op m))) from inferInstance
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono _

omit [PreservesFiniteLimits Φ] in
/-- If, at level `m`, `Φ` maps `ι` to a kernel of `Φ` of the differential `S (D + 1) ⟶ S (D + 2)`,
then `Φ` applied degreewise to the inclusion of the truncation is a quasi-isomorphism in degree
`D + 1`. -/
lemma map_truncationHom_quasiIsoAt_top (m : ℕ)
    (hker : IsLimit (KernelFork.ofι (Φ.map (ι.tower.app (op m)))
      (by rw [← Φ.map_comp, hιd, Φ.map_zero]) : Fork (Φ.map ((d (D + 1)).tower.app (op m))) 0)) :
    QuasiIsoAt ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m))) (D + 1) := by
  rw [quasiIsoAt_iff' _ D (D + 1) (D + 1 + 1) (CochainComplex.prev_nat_succ D)
    (CochainComplex.next ℕ (D + 1))]
  have := isIso_truncationInclusion_tower_app S D Z ι (le_refl D) (op m)
  have : Epi ((HomologicalComplex.shortComplexFunctor' E (ComplexShape.up ℕ) D (D + 1)
      (D + 1 + 1)).map ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m)))).τ₁ :=
    show Epi (Φ.map ((truncationInclusion S D Z ι D).tower.app (op m))) from inferInstance
  refine quasiIso_of_epi_of_isLimit_kernelFork _ ?_
    (KernelFork.isLimitOfIsLimitOfIff' hker _ fun W φ => ?_)
    (Φ.mapIso (eqToIso (show (truncationTerm S D Z (D + 1)).tower.obj (op m) = Z.tower.obj (op m)
      by rw [truncationTerm_of_eq S D Z rfl]))) ?_
  · exact (Φ.map_isZero (isZero_truncation_obj_X S d sq D Z p ι hpι m (by omega))).eq_of_tgt _ _
  · change _ ↔ φ ≫ Φ.map (((ofDegrees S d sq).obj m).d (D + 1) (D + 1 + 1)) = 0
    rw [ofDegrees_obj_d]
    exact Iff.rfl
  · change Φ.map ((truncationInclusion S D Z ι (D + 1)).tower.app (op m)) = _
    rw [truncationInclusion_tower_app_top, Φ.map_comp]
    rfl

/-- If, at level `m`, `Φ` maps `ι` to a kernel of `Φ` of the differential `S (D + 1) ⟶ S (D + 2)`,
then `Φ` applied degreewise to the inclusion of the truncation is a quasi-isomorphism in degrees
`≤ D + 1`. -/
lemma map_truncationHom_quasiIsoAt_of_le_succ (m : ℕ) {q : ℕ} (hq : q ≤ D + 1)
    (hker : IsLimit (KernelFork.ofι (Φ.map (ι.tower.app (op m)))
      (by rw [← Φ.map_comp, hιd, Φ.map_zero]) : Fork (Φ.map ((d (D + 1)).tower.app (op m))) 0)) :
    QuasiIsoAt ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((truncationHom S d sq D Z p ι hpι hιd).tower.app (op m))) q := by
  rcases Nat.lt_or_eq_of_le hq with hq | rfl
  · exact map_truncationHom_quasiIsoAt_of_le S d sq D Z p ι hpι hιd Φ m (Nat.lt_succ_iff.1 hq)
  · exact map_truncationHom_quasiIsoAt_top S d sq D Z p ι hpι hιd Φ m hker

end TruncationSections

section ResolutionSections

variable {C : Type u} [Category.{v} C] [Abelian C] {E : Type u'} [Category.{v'} E] [Abelian E]
  {ℓ : ℕ}
variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (η : 𝟭 C ⟶ F) [∀ X : C, Mono (η.app X)] (T : DivisibleSystem C ℓ) (D : ℕ)
  (Φ : C ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (h : m' ≤ m), Epi (Φ.map ((T.termSystem F η q).projection h)))
  (hres : ∀ {m' m : ℕ} (h : m' ≤ m),
    Epi (Φ.map ((T.residualSystem F η (D + 1)).projection h)))

/-- The tower `m ↦ Φ(F_m^•)` of section complexes of the resolution system. No surjectivity
of its transition maps is assumed, so it is only an inverse system. -/
abbrev resolutionSectionsTower : ℕᵒᵖ ⥤ CochainComplex E ℕ :=
  (T.resolutionSystem F η).tower ⋙ Φ.mapHomologicalComplex (ComplexShape.up ℕ)

/-- `Φ` applied degreewise to the inclusion of the truncated resolution system, as a morphism
of towers from the truncated section complexes to `resolutionSectionsTower`. -/
def truncatedResolutionSectionsTowerHom :
    (T.truncatedResolutionSectionsSystem F η D Φ hterm hres).tower ⟶
      T.resolutionSectionsTower F η Φ :=
  Functor.whiskerRight (T.truncatedResolutionHom F η D).tower
    (Φ.mapHomologicalComplex (ComplexShape.up ℕ))

/-- The components of `truncatedResolutionSectionsTowerHom` are `Φ` applied degreewise to the
components of the inclusion of the truncated resolution system. -/
lemma truncatedResolutionSectionsTowerHom_app (m : ℕᵒᵖ) :
    (T.truncatedResolutionSectionsTowerHom F η D Φ hterm hres).app m =
      (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((T.truncatedResolutionHom F η D).tower.app m) :=
  rfl

/-- At every level, `Φ` applied degreewise to the inclusion of the truncated resolution system is
a quasi-isomorphism in degrees `≤ D + 1`: in degree `D + 1`, `Φ` maps the residual inclusion
`R^(D + 1) ⟶ F^(D + 1)` to a kernel of `Φ(F^(D + 1)) ⟶ Φ(F^(D + 2))`. -/
lemma map_truncatedResolutionHom_quasiIsoAt (m : ℕᵒᵖ) {q : ℕ} (hq : q ≤ D + 1) :
    QuasiIsoAt ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((T.truncatedResolutionHom F η D).tower.app m)) q :=
  map_truncationHom_quasiIsoAt_of_le_succ _ _ _ D _ _ _ _
    (T.residualInclusion_termDifferential_tower_app F η (D + 1)) Φ (unop m) hq
    (T.mapResidualInclusionIsKernel F η Φ (D + 1) (unop m))

/-- At every level, the inclusion of the truncated section complexes is a quasi-isomorphism in
degrees `≤ D + 1`. -/
lemma truncatedResolutionSectionsTowerHom_quasiIsoAt (m : ℕᵒᵖ) {q : ℕ} (hq : q ≤ D + 1) :
    QuasiIsoAt ((T.truncatedResolutionSectionsTowerHom F η D Φ hterm hres).app m) q :=
  map_truncatedResolutionHom_quasiIsoAt F η T D Φ m hq

variable [HasLimitsOfShape ℕᵒᵖ E]

/-- For `n ≤ D + 1`, the inverse limit of the degree-`n` cohomologies of the truncated section
complexes is that of the full section complexes `Φ(F_m^•)`. -/
def truncatedResolutionSectionsAdicCohomologyIso {n : ℕ} (hn : n ≤ D + 1) :
    (T.truncatedResolutionSectionsSystem F η D Φ hterm hres).levelCohomologyLimit n ≅
      limit (T.resolutionSectionsTower F η Φ ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) :=
  haveI := isIso_limitHomologyMap (T.truncatedResolutionSectionsTowerHom F η D Φ hterm hres) n
    (fun m => T.truncatedResolutionSectionsTowerHom_quasiIsoAt F η D Φ hterm hres m hn)
  asIso (limitHomologyMap (T.truncatedResolutionSectionsTowerHom F η D Φ hterm hres) n)

end ResolutionSections

section SmoothGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ) {E : Type u'} [Category.{v'} E] [Abelian E]
  (Φ : SmoothTopologicalSheaf R G X ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))

/-- The tower `m ↦ Φ(F_m^•)` of section complexes of the smooth Godement resolutions of the
levels of `T`. No surjectivity of its transition maps is assumed. -/
abbrev smoothGodementSectionsTower : ℕᵒᵖ ⥤ CochainComplex E ℕ :=
  (smoothGodementResolutionSystem h T).tower ⋙ Φ.mapHomologicalComplex (ComplexShape.up ℕ)

/-- `Φ` applied degreewise to the inclusion of the truncated smooth Godement resolution system,
as a morphism of towers into `smoothGodementSectionsTower`. -/
def smoothGodementTruncatedSectionsTowerHom :
    (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).tower ⟶
      smoothGodementSectionsTower h T Φ :=
  Functor.whiskerRight (smoothGodementTruncatedResolutionHom h T D).tower
    (Φ.mapHomologicalComplex (ComplexShape.up ℕ))

/-- The components of `smoothGodementTruncatedSectionsTowerHom` are `Φ` applied degreewise to
the components of the inclusion of the truncated smooth Godement resolution system. -/
lemma smoothGodementTruncatedSectionsTowerHom_app (m : ℕᵒᵖ) :
    (smoothGodementTruncatedSectionsTowerHom h T D Φ hterm hres).app m =
      (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((smoothGodementTruncatedResolutionHom h T D).tower.app m) :=
  rfl

/-- At every level, the inclusion of the truncated smooth Godement section complexes is a
quasi-isomorphism in degrees `≤ D + 1`. -/
lemma smoothGodementTruncatedSectionsTowerHom_quasiIsoAt (m : ℕᵒᵖ) {q : ℕ} (hq : q ≤ D + 1) :
    QuasiIsoAt ((smoothGodementTruncatedSectionsTowerHom h T D Φ hterm hres).app m) q := by
  have := h.1
  have := h.2.1
  have := h.2.2
  exact truncatedResolutionSectionsTowerHom_quasiIsoAt (smoothZeroFunctor R G X)
    (smoothCoaugmentation R G X) T D Φ hterm hres m hq

variable [HasLimitsOfShape ℕᵒᵖ E]

/-- For `n ≤ D + 1`, the inverse limit of the degree-`n` cohomologies of the truncated smooth
Godement section complexes is that of the full ones. -/
def smoothGodementTruncatedSectionsAdicCohomologyIso {n : ℕ} (hn : n ≤ D + 1) :
    (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).levelCohomologyLimit n ≅
      limit (smoothGodementSectionsTower h T Φ ⋙
        HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n) :=
  haveI := isIso_limitHomologyMap (smoothGodementTruncatedSectionsTowerHom h T D Φ hterm hres) n
    (fun m => smoothGodementTruncatedSectionsTowerHom_quasiIsoAt h T D Φ hterm hres m hn)
  asIso (limitHomologyMap (smoothGodementTruncatedSectionsTowerHom h T D Φ hterm hres) n)

/-- Followed by the projection to level `m`, `smoothGodementTruncatedSectionsAdicCohomologyIso`
is the map induced on cohomology by the inclusion of the truncated section complex. -/
@[reassoc (attr := simp)]
lemma smoothGodementTruncatedSectionsAdicCohomologyIso_hom_π {n : ℕ} (hn : n ≤ D + 1) (m : ℕᵒᵖ) :
    (smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres hn).hom ≫
        limit.π _ m =
      limit.π _ m ≫ (HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n).map
        ((Φ.mapHomologicalComplex (ComplexShape.up ℕ)).map
          ((smoothGodementTruncatedResolutionHom h T D).tower.app m)) :=
  limitHomologyMap_π _ _ _

end SmoothGodement

section SmoothGodementAdic

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : Type u} [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] {ℓ : ℕ}
  (h : SmoothGodementZeroExactStatement R G X) (T : SmoothSheafDivisibleSystem R G X ℓ)
  (D : ℕ)

/-- Given `FiniteCohomologyInverseLimitStatement` and finite cohomology of the truncated section
complexes, for a sections functor `Φ` with values in `R'`-modules and `n ≤ D + 1`, the degree-`n`
cohomology of the `ℓ`-adic limit of the truncated smooth Godement section complexes is the
inverse limit of the degree-`n` cohomologies of the full section complexes `Φ(F_m^•)`. -/
def smoothGodementTruncatedSectionsAdicLimitHomologyIso {R' : Type u'} [Ring R']
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
    (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).adicLimit.homology n ≅
      limit (smoothGodementSectionsTower h T Φ ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{v'} R') (ComplexShape.up ℕ) n) :=
  haveI := isIso_adicLimitComparison_of_finite hS _ hfin n
  asIso (adicLimitComparison _ n) ≪≫
    smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres hn

/-- The representation version of `smoothGodementTruncatedSectionsAdicLimitHomologyIso`, for a
sections functor `Φ` with values in representations of a monoid `G'` over `k`. -/
def smoothGodementTruncatedSectionsAdicLimitHomologyIsoRep {k : Type u'} [CommRing k]
    {G' : Type w} [Monoid G'] (Φ : SmoothTopologicalSheaf R G X ⥤ Rep.{v'} k G') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h T q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h T (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{u', v'} k)
    (hfin : ∀ m n, Finite
      (((smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (smoothGodementTruncatedSectionsSystem h T D Φ hterm hres).adicLimit.homology n ≅
      limit (smoothGodementSectionsTower h T Φ ⋙
        HomologicalComplex.homologyFunctor (Rep.{v'} k G') (ComplexShape.up ℕ) n) :=
  haveI := isIso_adicLimitComparison_rep hS _ hfin n
  asIso (adicLimitComparison _ n) ≪≫
    smoothGodementTruncatedSectionsAdicCohomologyIso h T D Φ hterm hres hn

end SmoothGodementAdic

section SmoothGodementLemma28

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

/-- Every level of the truncated compact-section system vanishes in degrees `≥ D + 2`. -/
lemma isZero_smoothGodementTruncatedCompactSectionsSystem_obj_X (m q : ℕ) (hq : D + 2 ≤ q) :
    IsZero (((smoothGodementTruncatedCompactSectionsSystem h T D hterm hres).obj m).X q) :=
  isZero_smoothGodementTruncatedSectionsSystem_obj_X h T D (smoothSheafCompactSections R G X)
    hterm hres m (by omega)

/-- The tower `m ↦ Γ_c(F_m^•)` of compact-section complexes of the smooth Godement
resolutions of the levels of `T`, as complexes of representations of `G`. -/
abbrev smoothGodementCompactSectionsRepTower : ℕᵒᵖ ⥤ CochainComplex (Rep.{u} R G) ℕ :=
  (smoothGodementResolutionSystem h T).tower ⋙
    (smoothSheafCompactSections R G X).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      SmoothRep.toRep.mapHomologicalComplex (ComplexShape.up ℕ)

/-- The inclusion of the truncated compact-section complexes, as complexes of representations,
into `smoothGodementCompactSectionsRepTower`. -/
def smoothGodementCompactSectionsRepTowerHom :
    (smoothGodementTruncatedCompactSectionsSystem h T D hterm hres).toRepComplexes.tower ⟶
      smoothGodementCompactSectionsRepTower h T :=
  Functor.whiskerRight (smoothGodementTruncatedResolutionHom h T D).tower
    ((smoothSheafCompactSections R G X).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      SmoothRep.toRep.mapHomologicalComplex (ComplexShape.up ℕ))

/-- At every level, this inclusion is a quasi-isomorphism in degrees `≤ D + 1`. -/
lemma smoothGodementCompactSectionsRepTowerHom_quasiIsoAt (m : ℕᵒᵖ) {q : ℕ} (hq : q ≤ D + 1) :
    QuasiIsoAt ((smoothGodementCompactSectionsRepTowerHom h T D hterm hres).app m) q := by
  have := h.1
  have := h.2.1
  have := h.2.2
  exact map_truncatedResolutionHom_quasiIsoAt (smoothZeroFunctor R G X)
    (smoothCoaugmentation R G X) T D (smoothSheafCompactSections R G X ⋙ SmoothRep.toRep) m hq

variable {ι : Type u} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H) [∀ i, (H i).Normal]
  [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)] [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (hm : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map
      (((smoothGodementTruncatedCompactSectionsSystem h T D hterm hres).projection hm).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `lim C_m^•` for the compact-section complexes `G_m^•(U)` of the truncated smooth
Godement resolutions: `quotientInvariantsInverseLimit` with `N = D + 2`. -/
abbrev smoothGodementQuotientInvariantsInverseLimit : CochainComplex (Rep.{u} R G) ℤ :=
  quotientInvariantsInverseLimit.{0, u, u} (D + 2)
    (smoothGodementTruncatedCompactSectionsSystem h T D hterm hres) H hH hK hk

/-- The map of Harris's Lemma 2.8 for these complexes: `quotientInvariantsInverseLimitComparison`
with `N = D + 2`, the vanishing hypothesis being
`isZero_smoothGodementTruncatedCompactSectionsSystem_obj_X`. -/
abbrev smoothGodementQuotientInvariantsInverseLimitComparison (q : ℤ) :
    (smoothGodementQuotientInvariantsInverseLimit h T D hterm hres H hH hK hk).homology q ⟶
      limit ((smoothGodementTruncatedCompactSectionsSystem h T D hterm
        hres).toRepComplexes.extendSystem.tower ⋙
          HomologicalComplex.homologyFunctor (Rep.{u} R G) (ComplexShape.up ℤ) q) :=
  quotientInvariantsInverseLimitComparison.{0, u, u} (D + 2)
    (smoothGodementTruncatedCompactSectionsSystem h T D hterm hres) H hH hK hk
    (isZero_smoothGodementTruncatedCompactSectionsSystem_obj_X h T D hterm hres) q

/-- The published Lemma 2.8 (`isIso_quotientInvariantsInverseLimitComparison`) for these
complexes. -/
theorem isIso_smoothGodementQuotientInvariantsInverseLimitComparison
    (hS : ProPInvariantSubcomplexStatement.{u, u, u})
    (hS' : FiniteCohomologyInverseLimitStatement.{u, u} R) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : H i), (((smoothGodementTruncatedCompactSectionsSystem h T D hterm
      hres).toRepComplexes.obj m).homology q).ρ g = LinearMap.id)
    (hfin : ∀ m n, Finite (((smoothGodementTruncatedCompactSectionsSystem h T D hterm
      hres).toRepComplexes.obj m).homology n)) (q : ℤ) :
    IsIso (smoothGodementQuotientInvariantsInverseLimitComparison h T D hterm hres H hH hK hk q) :=
  isIso_quotientInvariantsInverseLimitComparison.{0, u, u} (D + 2) _ H hH hK hk hS hS' hP hR
    (isZero_smoothGodementTruncatedCompactSectionsSystem_obj_X h T D hterm hres) htriv hfin q

/-- Harris's Lemma 2.8 in degrees `n ≤ D + 1`, with the cohomology of the levels computed by the full
smooth Godement resolutions: under the hypotheses of
`isIso_smoothGodementQuotientInvariantsInverseLimitComparison`, the degree-`n` cohomology of
`lim C_m^•` is the inverse limit over `m` of the degree-`n` cohomologies of the compact-section
complexes `Γ_c(F_m^•)`. -/
def smoothGodementQuotientInvariantsInverseLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{u, u, u})
    (hS' : FiniteCohomologyInverseLimitStatement.{u, u} R) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : H i), (((smoothGodementTruncatedCompactSectionsSystem h T D hterm
      hres).toRepComplexes.obj m).homology q).ρ g = LinearMap.id)
    (hfin : ∀ m n, Finite (((smoothGodementTruncatedCompactSectionsSystem h T D hterm
      hres).toRepComplexes.obj m).homology n)) {n : ℕ} (hn : n ≤ D + 1) :
    (smoothGodementQuotientInvariantsInverseLimit h T D hterm hres H hH hK hk).homology n ≅
      limit (smoothGodementCompactSectionsRepTower h T ⋙
        HomologicalComplex.homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) n) :=
  haveI := isIso_smoothGodementQuotientInvariantsInverseLimitComparison h T D hterm hres H hH hK
    hk hS hS' hP hR htriv hfin n
  haveI := isIso_limitHomologyMap (smoothGodementCompactSectionsRepTowerHom h T D hterm hres) n
    (fun m => smoothGodementCompactSectionsRepTowerHom_quasiIsoAt h T D hterm hres m hn)
  asIso (smoothGodementQuotientInvariantsInverseLimitComparison h T D hterm hres H hH hK hk n) ≪≫
    extendLevelCohomologyLimitIso _ n ≪≫
    asIso (limitHomologyMap (smoothGodementCompactSectionsRepTowerHom h T D hterm hres) n)

end SmoothGodementLemma28

section ConstantGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X] (h : SmoothGodementZeroExactStatement R G X) (D : ℕ)
  {E : Type u'} [Category.{v'} E] [Abelian E]
  (Φ : SmoothTopologicalSheaf R G X ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ]

/-- The tower `m ↦ Φ(F_m^•)` of section complexes of the smooth Godement resolutions of the
constant sheaves `R / ℓ ^ m R`. -/
abbrev constantGodementSectionsTower : ℕᵒᵖ ⥤ CochainComplex E ℕ :=
  smoothGodementSectionsTower h (constantSheafSystem hℓ G X) Φ

/-- Level `m` of `constantGodementSectionsTower` is `Φ` applied degreewise to the smooth
Godement complex of the locally constant sheaf of `R / ℓ ^ m R`. -/
def constantGodementSectionsTowerObjIso (m : ℕ) :
    (constantGodementSectionsTower hℓ G X h Φ).obj (op m) ≅
      (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (smoothComplex R G X (constantLevelSheaf R ℓ G X m)) :=
  (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (constantGodementResolutionSystemObjIso hℓ G X h m)

variable [HasLimitsOfShape ℕᵒᵖ E]

/-- The `ℓ`-adic cohomology `lim_m H^n(Φ(F_m^•))` of the constant system: the inverse limit over
`m` of the degree-`n` cohomologies of the section complexes of the smooth Godement resolutions
of `R / ℓ ^ m R`. -/
abbrev constantGodementAdicCohomology (n : ℕ) : E :=
  limit (constantGodementSectionsTower hℓ G X h Φ ⋙
    HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n)

variable
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi (Φ.map ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi (Φ.map
      ((smoothGodementResidualSystem h (constantSheafSystem hℓ G X) (D + 1)).projection hm)))

/-- Harris's `ℓ`-adic section complex `lim_m G_m^•(U)` for the constant system: the `ℓ`-adic
limit of the truncated constant section complexes. -/
abbrev constantGodementAdicSectionsComplex : CochainComplex E ℤ :=
  (constantGodementTruncatedSectionsSystem hℓ G X h D Φ hterm hres).adicLimit

/-- For `n ≤ D + 1`, the inverse limit of the degree-`n` cohomologies of the truncated constant
section complexes is the `ℓ`-adic cohomology `constantGodementAdicCohomology`. -/
def constantGodementAdicCohomologyIso {n : ℕ} (hn : n ≤ D + 1) :
    (constantGodementTruncatedSectionsSystem hℓ G X h D Φ hterm hres).levelCohomologyLimit n ≅
      constantGodementAdicCohomology hℓ G X h Φ n :=
  smoothGodementTruncatedSectionsAdicCohomologyIso h _ D Φ hterm hres hn

end ConstantGodement

section ConstantGodementAdic

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable {R : Type u} [CommRing R] {ℓ : ℕ} (hℓ : IsSMulRegular R (ℓ : R))
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X] (h : SmoothGodementZeroExactStatement R G X) (D : ℕ)

/-- For a sections functor `Φ` with values in `R'`-modules, given
`FiniteCohomologyInverseLimitStatement` and finite cohomology of the truncated constant section
complexes, for `n ≤ D + 1` the degree-`n` cohomology of `lim_m G_m^•(U)` is the `ℓ`-adic cohomology
`lim_m H^n(Φ(F_m^•))` of the constant system. -/
def constantGodementAdicLimitHomologyIso {R' : Type u'} [Ring R']
    (Φ : SmoothTopologicalSheaf R G X ⥤ ModuleCat.{v'} R') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map
        ((smoothGodementResidualSystem h (constantSheafSystem hℓ G X) (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{u', v'} R')
    (hfin : ∀ m n, Finite
      (((constantGodementTruncatedSectionsSystem hℓ G X h D Φ hterm hres).obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (constantGodementAdicSectionsComplex hℓ G X h D Φ hterm hres).homology n ≅
      constantGodementAdicCohomology hℓ G X h Φ n :=
  smoothGodementTruncatedSectionsAdicLimitHomologyIso h _ D Φ hterm hres hS hfin hn

/-- The representation version of `constantGodementAdicLimitHomologyIso`. -/
def constantGodementAdicLimitHomologyIsoRep {k : Type u'} [CommRing k] {G' : Type w}
    [Monoid G'] (Φ : SmoothTopologicalSheaf R G X ⥤ Rep.{v'} k G') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map
        ((smoothGodementResidualSystem h (constantSheafSystem hℓ G X) (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{u', v'} k)
    (hfin : ∀ m n, Finite
      (((constantGodementTruncatedSectionsSystem hℓ G X h D Φ hterm hres).obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (constantGodementAdicSectionsComplex hℓ G X h D Φ hterm hres).homology n ≅
      constantGodementAdicCohomology hℓ G X h Φ n :=
  smoothGodementTruncatedSectionsAdicLimitHomologyIsoRep h _ D Φ hterm hres hS hfin hn

variable
  (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementTermSystem h (constantSheafSystem hℓ G X) q).projection hm)))
  (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
    Epi ((smoothSheafCompactSections R G X).map
      ((smoothGodementResidualSystem h (constantSheafSystem hℓ G X) (D + 1)).projection hm)))
  {ι : Type u} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H) [∀ i, (H i).Normal]
  [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)] [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (hm : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map
      (((constantGodementTruncatedCompactSectionsSystem hℓ G X h D hterm hres).projection
        hm).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Harris's `lim C_m^•` for the constant system `{R / ℓ ^ m R}`. -/
abbrev constantQuotientInvariantsInverseLimit : CochainComplex (Rep.{u} R G) ℤ :=
  smoothGodementQuotientInvariantsInverseLimit h (constantSheafSystem hℓ G X) D hterm hres H hH
    hK hk

/-- Harris's Lemma 2.8 for the constant system in degrees `n ≤ D + 1`: the degree-`n` cohomology of
`lim C_m^•` is the inverse limit over `m` of the degree-`n` cohomologies of the compact-section
complexes of the smooth Godement resolutions of `R / ℓ ^ m R`. -/
def constantQuotientInvariantsInverseLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{u, u, u})
    (hS' : FiniteCohomologyInverseLimitStatement.{u, u} R) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (htriv : ∀ m i q (g : H i), (((constantGodementTruncatedCompactSectionsSystem hℓ G X h D
      hterm hres).toRepComplexes.obj m).homology q).ρ g = LinearMap.id)
    (hfin : ∀ m n, Finite (((constantGodementTruncatedCompactSectionsSystem hℓ G X h D hterm
      hres).toRepComplexes.obj m).homology n)) {n : ℕ} (hn : n ≤ D + 1) :
    (constantQuotientInvariantsInverseLimit hℓ G X h D hterm hres H hH hK hk).homology n ≅
      limit (smoothGodementCompactSectionsRepTower h (constantSheafSystem hℓ G X) ⋙
        HomologicalComplex.homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) n) :=
  smoothGodementQuotientInvariantsInverseLimitHomologyIso h _ D hterm hres H hH hK hk hS hS' hP
    hR htriv hfin hn

end ConstantGodementAdic

section IntConstantGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable (ℓ : ℕ) (hℓ : ℓ ≠ 0) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type) [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  [HasStableNeighbourhoods G X] (h : SmoothGodementZeroExactStatement ℤ G X) (D : ℕ)

/-- The tower `m ↦ Φ(F_m^•)` of section complexes of the smooth Godement resolutions of the
constant sheaves `ℤ / ℓ ^ m ℤ`. -/
abbrev intConstantGodementSectionsTower {E : Type u'} [Category.{v'} E] [Abelian E]
    (Φ : SmoothTopologicalSheaf ℤ G X ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ] :
    ℕᵒᵖ ⥤ CochainComplex E ℕ :=
  smoothGodementSectionsTower h (intConstantSheafSystem ℓ hℓ G X) Φ

/-- Level `m` of `intConstantGodementSectionsTower` is `Φ` applied degreewise to the smooth
Godement complex of the locally constant sheaf of `ZMod (ℓ ^ m)`. -/
def intConstantGodementSectionsTowerObjIso {E : Type u'} [Category.{v'} E] [Abelian E]
    (Φ : SmoothTopologicalSheaf ℤ G X ⥤ E) [Φ.Additive] [PreservesFiniteLimits Φ] (m : ℕ) :
    (intConstantGodementSectionsTower ℓ hℓ G X h Φ).obj (op m) ≅
      (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (smoothComplex ℤ G X ((LocallyConstantSheaf.smoothFunctor ℤ G X).obj
          ((smoothTrivialFunctor.{0, 0, 0} ℤ G).obj (ModuleCat.of ℤ (ZMod (ℓ ^ m)))))) :=
  (Φ.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso
    (smoothGodementResolutionSystemObjIsoOfIso h _ m (intConstantSheafSystemObjIso ℓ hℓ G X m))

/-- Harris's `ℓ`-adic cohomology `lim_m H^n(Φ(F_m^•))` for the constant sheaves
`ℤ / ℓ ^ m ℤ`. -/
abbrev intConstantGodementAdicCohomology {E : Type u'} [Category.{v'} E] [Abelian E]
    [HasLimitsOfShape ℕᵒᵖ E] (Φ : SmoothTopologicalSheaf ℤ G X ⥤ E) [Φ.Additive]
    [PreservesFiniteLimits Φ] (n : ℕ) : E :=
  limit (intConstantGodementSectionsTower ℓ hℓ G X h Φ ⋙
    HomologicalComplex.homologyFunctor E (ComplexShape.up ℕ) n)

/-- Harris's `ℓ`-adic section complex `lim_m G_m^•(U)` for the constant sheaves
`ℤ / ℓ ^ m ℤ`. -/
abbrev intConstantGodementAdicSectionsComplex {E : Type u'} [Category.{v'} E] [Abelian E]
    [HasLimitsOfShape ℕᵒᵖ E] (Φ : SmoothTopologicalSheaf ℤ G X ⥤ E) [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (intConstantSheafSystem ℓ hℓ G X) q).projection
        hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h (intConstantSheafSystem ℓ hℓ G X)
        (D + 1)).projection hm))) :
    CochainComplex E ℤ :=
  (intConstantGodementTruncatedSectionsSystem ℓ hℓ G X h D Φ hterm hres).adicLimit

/-- For a sections functor `Φ` with values in `R'`-modules, given
`FiniteCohomologyInverseLimitStatement` and finite cohomology of the truncated section complexes
for `ℤ / ℓ ^ m ℤ`, for `n ≤ D + 1` the degree-`n` cohomology of `lim_m G_m^•(U)` is the `ℓ`-adic
cohomology `lim_m H^n(Φ(F_m^•))`. -/
def intConstantGodementAdicLimitHomologyIso {R' : Type u'} [Ring R']
    (Φ : SmoothTopologicalSheaf ℤ G X ⥤ ModuleCat.{v'} R') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (intConstantSheafSystem ℓ hℓ G X) q).projection
        hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h (intConstantSheafSystem ℓ hℓ G X)
        (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{u', v'} R')
    (hfin : ∀ m n, Finite
      (((intConstantGodementTruncatedSectionsSystem ℓ hℓ G X h D Φ hterm hres).obj m).homology
        n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (intConstantGodementAdicSectionsComplex ℓ hℓ G X h D Φ hterm hres).homology n ≅
      intConstantGodementAdicCohomology ℓ hℓ G X h Φ n :=
  smoothGodementTruncatedSectionsAdicLimitHomologyIso h _ D Φ hterm hres hS hfin hn

/-- The representation version of `intConstantGodementAdicLimitHomologyIso`. -/
def intConstantGodementAdicLimitHomologyIsoRep {k : Type u'} [CommRing k] {G' : Type w}
    [Monoid G'] (Φ : SmoothTopologicalSheaf ℤ G X ⥤ Rep.{v'} k G') [Φ.Additive]
    [PreservesFiniteLimits Φ]
    (hterm : ∀ q ≤ D, ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementTermSystem h (intConstantSheafSystem ℓ hℓ G X) q).projection
        hm)))
    (hres : ∀ {m' m : ℕ} (hm : m' ≤ m),
      Epi (Φ.map ((smoothGodementResidualSystem h (intConstantSheafSystem ℓ hℓ G X)
        (D + 1)).projection hm)))
    (hS : FiniteCohomologyInverseLimitStatement.{u', v'} k)
    (hfin : ∀ m n, Finite
      (((intConstantGodementTruncatedSectionsSystem ℓ hℓ G X h D Φ hterm hres).obj m).homology
        n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (intConstantGodementAdicSectionsComplex ℓ hℓ G X h D Φ hterm hres).homology n ≅
      intConstantGodementAdicCohomology ℓ hℓ G X h Φ n :=
  smoothGodementTruncatedSectionsAdicLimitHomologyIsoRep h _ D Φ hterm hres hS hfin hn

end IntConstantGodement

section PadicCoefficients

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `ℓ` is a non-zero-divisor in the `ℓ`-adic integers `ℤ_[ℓ]`. -/
lemma padicInt_isSMulRegular : IsSMulRegular ℤ_[ℓ] ((ℓ : ℕ) : ℤ_[ℓ]) :=
  (IsRegular.of_ne_zero (Nat.cast_ne_zero.2 (Fact.out : ℓ.Prime).ne_zero)).left.isSMulRegular

variable {ℓ} in
/-- A natural number prime to `ℓ` is a unit in the `ℓ`-adic integers. -/
lemma padicInt_isUnit_natCast {n : ℕ} (hn : ℓ.Coprime n) : IsUnit ((n : ℕ) : ℤ_[ℓ]) :=
  PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 hn)

variable {ℓ} in
/-- A prime `p ≠ ℓ` is prime to `ℓ`; with `padicInt_isUnit_natCast` it is a unit in `ℤ_[ℓ]`. -/
lemma coprime_of_prime_ne {p : ℕ} (hp : p.Prime) (hpℓ : p ≠ ℓ) : ℓ.Coprime p :=
  (Nat.coprime_primes Fact.out hp).2 hpℓ.symm

/-- The level rings `ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ]` of the constant system over `ℤ_[ℓ]` are the rings
`ZMod (ℓ ^ m)`, through Mathlib's reduction `PadicInt.toZModPow m`, whose kernel is
`ℓ ^ m ℤ_[ℓ]`. -/
def padicLevelRingEquiv (m : ℕ) :
    ℤ_[ℓ] ⧸ Ideal.span {((ℓ : ℕ) : ℤ_[ℓ]) ^ m} ≃+* ZMod (ℓ ^ m) :=
  (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow m).symm).trans
    (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZModPow m)))

end PadicCoefficients

section PadicConstantGodement

open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Godement
  Langlands.Cohomology.SmoothGodement

variable (ℓ : ℕ) [Fact ℓ.Prime] (G : Type) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : Type) [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]
  (h : SmoothGodementZeroExactStatement ℤ_[ℓ] G X) (D : ℕ)
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

/-- Harris's `lim C_m^•` with `ℓ`-adic coefficients: the case `R = ℤ_[ℓ]` of
`constantQuotientInvariantsInverseLimit`, whose levels are the constant sheaves of
`ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ]` (the rings `ZMod (ℓ ^ m)` by `padicLevelRingEquiv`). The orders of the
transition kernels are assumed prime to `ℓ`, hence units in `ℤ_[ℓ]`. -/
abbrev padicConstantQuotientInvariantsInverseLimit : CochainComplex (Rep.{0} ℤ_[ℓ] G) ℤ :=
  constantQuotientInvariantsInverseLimit (padicInt_isSMulRegular ℓ) G X h D hterm hres H hH hK
    (fun hij => padicInt_isUnit_natCast (hk hij))

/-- Harris's Lemma 2.8 with `ℓ`-adic coefficients in degrees `n ≤ D + 1`: for a family of pro-`p`
subgroups with `p` prime to `ℓ`, under the remaining hypotheses of
`constantQuotientInvariantsInverseLimitHomologyIso`, the degree-`n` cohomology of `lim C_m^•` is
the inverse limit over `m` of the degree-`n` cohomologies of the compact-section complexes of the
smooth Godement resolutions of the constant sheaves of `ℤ_[ℓ] / ℓ ^ m ℤ_[ℓ]`. -/
def padicConstantQuotientInvariantsInverseLimitHomologyIso
    (hS : ProPInvariantSubcomplexStatement.{0, 0, 0})
    (hS' : FiniteCohomologyInverseLimitStatement.{0, 0} ℤ_[ℓ]) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hpℓ : ℓ.Coprime p)
    (htriv : ∀ m i q (g : H i), (((constantGodementTruncatedCompactSectionsSystem
      (padicInt_isSMulRegular ℓ) G X h D hterm hres).toRepComplexes.obj m).homology q).ρ g =
        LinearMap.id)
    (hfin : ∀ m n, Finite (((constantGodementTruncatedCompactSectionsSystem
      (padicInt_isSMulRegular ℓ) G X h D hterm hres).toRepComplexes.obj m).homology n))
    {n : ℕ} (hn : n ≤ D + 1) :
    (padicConstantQuotientInvariantsInverseLimit ℓ G X h D hterm hres H hH hK hk).homology n ≅
      limit (smoothGodementCompactSectionsRepTower h
          (constantSheafSystem (padicInt_isSMulRegular ℓ) G X) ⋙
        HomologicalComplex.homologyFunctor (Rep.{0} ℤ_[ℓ] G) (ComplexShape.up ℕ) n) :=
  constantQuotientInvariantsInverseLimitHomologyIso (padicInt_isSMulRegular ℓ) G X h D hterm hres
    H hH hK (fun hij => padicInt_isUnit_natCast (hk hij)) hS hS' hP (padicInt_isUnit_natCast hpℓ)
    htriv hfin hn

end PadicConstantGodement

end DivisibleSystem

end Langlands.Cohomology
