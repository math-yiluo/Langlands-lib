import Langlands.Cohomology.RestrictedProduct
import Langlands.GaloisCohomology.Global.BrauerSequence.HigherDegrees.LocalUnits
import Langlands.ClassFieldTheory.Global.IdeleArchimedean
import Langlands.ClassFieldTheory.Global.IntegralIdeleHerbrand

/-!
# The cohomology of the idèles of a finite Galois extension is local

Let `E / F` be a finite Galois extension of number fields and `J_E` its idèle group, a
representation of `Gal(E/F)`. Choose a finite place `wf v` of `E` above every finite place `v` of
`F` and an infinite place `wi v` above every infinite place `v`. Through the semilocal projections
`J_E → Coind(E_wˣ)` (the Library's `ideleSemilocalProjection` and `infiniteSemilocalProjection`),
`J_E` is the restricted product of the coinduced modules `Coind(E_wˣ)` of all places of `F` with
respect to the modules `Coind(U_w)` at the finite places (`isRestrictedProduct_ideleBlock`). Since
the valuation units of an unramified completion are cohomologically trivial, a class of
`Hⁿ⁺¹(Gal(E/F), J_E)` whose local components `Hⁿ⁺¹(Gal(E/F), J_E) → Hⁿ⁺¹(D_w, E_wˣ)` all vanish is
zero (`eq_zero_of_ideleLocalMap_eq_zero`). This is the injectivity half of the isomorphism
`Hⁿ(Gal(E/F), J_E) ≅ ⊕_v Hⁿ(D_w, E_wˣ)`, `n ≥ 1` (Neukirch–Schmidt–Wingberg (8.1.7); Tate in
Cassels–Fröhlich, VII §7).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Limits NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ClassFieldTheory.Global Langlands.ClassFieldTheory.Local
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic FundamentalClass
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

noncomputable section

section InfinitePlaces

variable {F E : Type u} [Field F] [Field E] [Algebra F E]

/-- Moving an infinite place by an element of `Gal(E/F)` does not change the place of `F` below. -/
theorem comap_infinitePlaceEquiv (g : E ≃ₐ[F] E) (w : InfinitePlace E) :
    (infinitePlaceEquiv g.toRingEquiv w).comap (algebraMap F E) = w.comap (algebraMap F E) := by
  ext x
  rw [InfinitePlace.comap_apply, InfinitePlace.comap_apply, infinitePlaceEquiv_apply]
  exact congrArg w (g.commutes x)

/-- `Gal(E/F)` acts transitively on the infinite places of `E` above a place of `F`. -/
theorem exists_infinitePlaceEquiv_eq [NumberField E] [IsGalois F E] {w w' : InfinitePlace E}
    (h : w.comap (algebraMap F E) = w'.comap (algebraMap F E)) :
    ∃ g : E ≃ₐ[F] E, infinitePlaceEquiv g.toRingEquiv w = w' := by
  obtain ⟨σ, hσ⟩ := InfinitePlace.exists_smul_eq_of_comap_eq h
  refine ⟨σ⁻¹, ?_⟩
  rw [infinitePlaceEquiv_eq_inv_smul, inv_inv, hσ]

end InfinitePlaces


variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

section Blocks

variable (wf : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
  [hwf : ∀ v, (wf v).asIdeal.LiesOver v.asIdeal] (wi : InfinitePlace F → InfinitePlace E)

/-- The block of `J_E` at a place of `F`: `Coind(E_wˣ)` along `decompositionHom v (wf v)` at a finite
place, along the stabilizer of `wi v` at an infinite place. -/
abbrev ideleBlock : HeightOneSpectrum (𝓞 F) ⊕ InfinitePlace F →
    Rep.{u} NormalizedTwoCocycle.CoefficientScalars.{u} (E ≃ₐ[F] E)
  | .inl v => Rep.coind (decompositionHom v (wf v))
      (unitsRepresentation (padicField v).Carrier ((wf v).adicCompletion E))
  | .inr v => Rep.coind (MulAction.stabilizer (E ≃ₐ[F] E) (wi v)).subtype
      (infiniteLocalRepresentation F (wi v))

/-- The integral part of the block: `Coind(U_w)` at a finite place, the whole block at an infinite
place. -/
abbrev ideleIntegralBlock : HeightOneSpectrum (𝓞 F) ⊕ InfinitePlace F →
    Rep.{u} NormalizedTwoCocycle.CoefficientScalars.{u} (E ≃ₐ[F] E)
  | .inl v => Rep.coind (decompositionHom v (wf v)) (localUnitsRepresentation v (wf v))
  | .inr v => Rep.coind (MulAction.stabilizer (E ≃ₐ[F] E) (wi v)).subtype
      (infiniteLocalRepresentation F (wi v))

/-- The inclusion of the integral part of a block. -/
abbrev ideleIntegralBlockInclusion :
    ∀ i, ideleIntegralBlock wf wi i ⟶ ideleBlock wf wi i
  | .inl v => coindLocalUnitsInclusion v (wf v)
  | .inr _ => 𝟙 _

/-- The projection of `J_E` to a block: the semilocal projection. -/
abbrev ideleBlockProjection :
    ∀ i, relativeIdeleRepresentation F E ⟶ ideleBlock wf wi i
  | .inl v => ideleSemilocalProjection v (wf v)
  | .inr v => infiniteSemilocalProjection F (wi v)

variable (hwi : ∀ v, (wi v).comap (algebraMap F E) = v)

include hwi in
/-- Two ideles whose projections to all blocks agree are equal. -/
theorem eq_of_ideleBlockProjection_eq {x y : (relativeIdeleRepresentation F E).V}
    (h : ∀ i, (ideleBlockProjection wf wi i).hom x = (ideleBlockProjection wf wi i).hom y) :
    x = y := by
  apply (@Additive.toMul (IdeleGroup (𝓞 E) E)).injective
  apply idele_ext
  · funext u
    obtain ⟨g, hg⟩ := exists_infinitePlaceEquiv_eq (hwi (u.comap (algebraMap F E)))
    have := ideleInfiniteCoordinate_eq_of_infiniteSemilocalProjection_eq (wi _)
      (h (.inr (u.comap (algebraMap F E)))) g
    rw [hg] at this
    exact congrArg Units.val this
  · intro u
    exact ideleCoordinate_eq_of_ideleSemilocalProjection_eq (placeBelow F u)
      (wf (placeBelow F u)) (h (.inl (placeBelow F u))) u

/-- If all coordinates of `x` above `v` are valuation units, so are all values of its semilocal
projection at `w | v`. -/
theorem ideleSemilocalProjection_mem_localUnits (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal]
    (x : (relativeIdeleRepresentation F E).V)
    (hx : ∀ (u : HeightOneSpectrum (𝓞 E)) [u.asIdeal.LiesOver v.asIdeal],
      ideleCoordinate u (@Additive.toMul (IdeleGroup (𝓞 E) E) x) ∈ localUnits u)
    (g : E ≃ₐ[F] E) :
    Additive.toMul (((ideleSemilocalProjection v w).hom x).1 g) ∈ localUnits w := by
  have := liesOver_finitePlaceEquiv v w g
  have hk := hx (finitePlaceEquiv g.toRingEquiv w)
  change ideleCoordinate w (relativeIdeleAut F E g
    (@Additive.toMul (IdeleGroup (𝓞 E) E) x)) ∈ localUnits w
  rw [mem_localUnits_iff] at hk ⊢
  rw [ideleCoordinate_relativeIdeleAut, finiteCompletionEquiv_valuation]
  exact hk

omit [NumberField F] [NumberField E] [IsGalois F E] in
/-- The finite places of `F` with some place above them in a finite set of places of `E` form a
finite set. -/
theorem finite_placeBelow_image (T : Set (HeightOneSpectrum (𝓞 E))) (hT : T.Finite) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ u ∈ T, placeBelow F u = v}.Finite :=
  (hT.image (placeBelow F)).subset fun _ ⟨u, hu, huv⟩ => ⟨u, hu, huv⟩

omit [IsGalois F E] in
/-- The finite places of `E` above a finite set of places of `F` form a finite set. -/
theorem finite_placeBelow_preimage (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    {u : HeightOneSpectrum (𝓞 E) | placeBelow F u ∈ S}.Finite := by
  refine (hS.biUnion fun v _ => (Set.finite_range
    (fun q : FinitePlacesAbove E v => (q.1 : HeightOneSpectrum (𝓞 E))))).subset ?_
  intro u hu
  exact Set.mem_biUnion hu ⟨⟨u, inferInstance⟩, rfl⟩

include hwi in
/-- **The idèles as a restricted product.** `J_E` is the restricted product of the blocks of the
places of `F`, with respect to the integral blocks. -/
theorem isRestrictedProduct_ideleBlock :
    Cohomology.IsRestrictedProduct (ideleBlockProjection wf wi) (ideleIntegralBlockInclusion wf wi) where
  injective i := by
    rcases i with v | v
    · exact coindLocalUnitsInclusion_injective v (wf v)
    · exact fun _ _ h => h
  eq_zero x hx := eq_of_ideleBlockProjection_eq wf wi hwi fun i => by rw [hx i, map_zero]
  finite x := by
    classical
    refine (finite_placeBelow_image (F := F) _ (finite_setOf_ideleCoordinate_not_mem_localUnits
      (@Additive.toMul (IdeleGroup (𝓞 E) E) x))).image Sum.inl |>.subset ?_
    rintro (v | v) hv
    · refine ⟨v, ?_, rfl⟩
      by_contra hcon
      apply hv
      refine exists_coindLocalUnitsInclusion_eq v (wf v) _
        (ideleSemilocalProjection_mem_localUnits v (wf v) x (fun u hu => ?_))
      by_contra hu'
      exact hcon ⟨u, hu', placeBelow_eq v u⟩
    · exact absurd ⟨_, rfl⟩ hv
  exists_eq p hp := by
    classical
    have hfin : ∀ v, Fintype ((E ≃ₐ[F] E) ⧸ (decompositionHom v (wf v)).range) :=
      fun v => Fintype.ofFinite _
    have hinf : ∀ v, Fintype ((E ≃ₐ[F] E) ⧸
        (MulAction.stabilizer (E ≃ₐ[F] E) (wi v)).subtype.range) :=
      fun v => Fintype.ofFinite _
    -- the semilocal sections of the components
    let s : HeightOneSpectrum (𝓞 F) → IdeleGroup (𝓞 E) E := fun v =>
      @Additive.toMul (IdeleGroup (𝓞 E) E) ((ideleSemilocalSection v (wf v)).hom (p (.inl v)))
    let t : InfinitePlace F → IdeleGroup (𝓞 E) E := fun v =>
      @Additive.toMul (IdeleGroup (𝓞 E) E) ((infiniteSemilocalSection F (wi v)).hom (p (.inr v)))
    let a : ∀ u : HeightOneSpectrum (𝓞 E), (u.adicCompletion E)ˣ :=
      fun u => ideleCoordinate u (s (placeBelow F u))
    let b : ∀ u : InfinitePlace E, (u.Completion)ˣ :=
      fun u => ideleInfiniteCoordinate u (t (u.comap (algebraMap F E)))
    -- the set of bad finite places of `F`
    let S : Set (HeightOneSpectrum (𝓞 F)) := {v | p (.inl v) ∉ Set.range
      (ideleIntegralBlockInclusion wf wi (.inl v)).hom}
    have hS : S.Finite := (hp.preimage Sum.inl_injective.injOn)
    have ha : {u | a u ∉ localUnits u}.Finite := by
      refine (finite_placeBelow_preimage S hS).subset fun u hu => ?_
      by_contra huS
      apply hu
      obtain ⟨c, hc⟩ := not_not.1 huS
      refine ideleCoordinate_mem_localUnits_of_ideleSemilocalProjection (placeBelow F u)
        (wf (placeBelow F u)) _ (fun g => ?_) u
      rw [ideleSemilocalProjection_ideleSemilocalSection, ← hc]
      exact (Additive.toMul (c.1 g)).2
    refine ⟨Additive.ofMul (ideleOfCoordinates a ha * ideleOfInfiniteCoordinates b), ?_⟩
    rintro (v | v)
    · -- finite places: compare with the semilocal section
      change (ideleSemilocalProjection v (wf v)).hom _ = p (.inl v)
      conv_rhs => rw [← ideleSemilocalProjection_ideleSemilocalSection v (wf v) (p (.inl v))]
      apply Subtype.ext
      funext g
      refine congrArg Additive.ofMul (ideleCoordinate_relativeIdeleAut_eq v g (fun u hu => ?_) (wf v))
      change ideleCoordinate u (ideleOfCoordinates a ha * ideleOfInfiniteCoordinates b) = _
      rw [map_mul, ideleCoordinate_ideleOfCoordinates,
        ideleCoordinate_ideleOfInfiniteCoordinates,
        mul_one]
      change ideleCoordinate u (s (placeBelow F u)) = _
      rw [placeBelow_eq v u]
    · -- infinite places: compare with the semilocal section
      change (infiniteSemilocalProjection F (wi v)).hom _ = p (.inr v)
      conv_rhs => rw [← infiniteSemilocalProjection_infiniteSemilocalSection (wi v) (p (.inr v))]
      apply Subtype.ext
      funext g
      refine congrArg Additive.ofMul
        ((ideleInfiniteCoordinate_relativeIdeleAut_eq_iff g (wi v) _ _).2 ?_)
      change ideleInfiniteCoordinate _ (ideleOfCoordinates a ha * ideleOfInfiniteCoordinates b) = _
      rw [map_mul, IntegralIdeleHerbrand.ideleInfiniteCoordinate_ideleOfCoordinates,
        ideleInfiniteCoordinate_ideleOfInfiniteCoordinates, one_mul]
      change ideleInfiniteCoordinate _ (t _) = _
      rw [comap_infinitePlaceEquiv, hwi v]

end Blocks

section Injectivity

variable (wf : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
  [hwf : ∀ v, (wf v).asIdeal.LiesOver v.asIdeal] (wi : InfinitePlace F → InfinitePlace E)
  (hwi : ∀ v, (wi v).comap (algebraMap F E) = v)

/-- The local component `Hⁿ(Gal(E/F), J_E) → Hⁿ(D_w, E_wˣ)` at an infinite place `w` of `E`:
restriction to the stabilizer of `w` followed by the `w`-coordinate. -/
abbrev ideleInfiniteLocalMap (w : InfinitePlace E) (n : ℕ) :
    relativeIdeleCohomology F E n ⟶ groupCohomology (infiniteLocalRepresentation F w) n :=
  groupCohomology.map (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype
    (infiniteLocalProjection F w) n

/-- If the local map at `w | v` kills `x`, so does the map to the block of `v`. -/
theorem map_ideleSemilocalProjection_eq_zero (v : HeightOneSpectrum (𝓞 F))
    (w : HeightOneSpectrum (𝓞 E)) [w.asIdeal.LiesOver v.asIdeal] (n : ℕ)
    (x : relativeIdeleCohomology F E n) (hx : ideleLocalMap v w n x = 0) :
    groupCohomology.map (MonoidHom.id _) (ideleSemilocalProjection v w) n x = 0 := by
  have hinj : Function.Injective (Shapiro.shapiroMapOf (decompositionHom v w)
      (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)) n) := by
    have := Shapiro.isIso_shapiroMapOf (decompositionHom_injective v w)
      (unitsRepresentation (padicField v).Carrier (w.adicCompletion E)) n
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [map_zero, ← ConcreteCategory.comp_apply, ← ideleLocalMap_eq]
  exact hx

omit [NumberField F] [IsGalois F E] in
/-- If the local map at an infinite place `w` kills `x`, so does the map to its block. -/
theorem map_infiniteSemilocalProjection_eq_zero (w : InfinitePlace E) (n : ℕ)
    (x : relativeIdeleCohomology F E n) (hx : ideleInfiniteLocalMap w n x = 0) :
    groupCohomology.map (MonoidHom.id _) (infiniteSemilocalProjection F w) n x = 0 := by
  have hinj : Function.Injective (Shapiro.shapiroMapOf
      (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype (infiniteLocalRepresentation F w) n) := by
    have := Shapiro.isIso_shapiroMapOf (Subgroup.subtype_injective _)
      (infiniteLocalRepresentation F w) n
    exact (ModuleCat.mono_iff_injective _).1 inferInstance
  apply hinj
  rw [map_zero, ← ConcreteCategory.comp_apply, map_infiniteSemilocalProjection_comp_shapiroMapOf]
  exact hx

omit [IsGalois F E] in
/-- The finite places of `F` whose chosen place above is ramified form a finite set. -/
theorem finite_setOf_ramified_wf :
    {v : HeightOneSpectrum (𝓞 F) | (wf v).asIdeal.ramificationIdx (𝓞 F) ≠ 1}.Finite :=
  (finite_placeBelow_image _ (finite_setOf_ramificationIdx_ne_one F E)).subset
    fun v hv => ⟨wf v, hv, placeBelow_eq v (wf v)⟩

/-- The integral blocks with nonzero cohomology in degree `n + 1` are finitely many. -/
theorem finite_not_isZero_ideleIntegralBlock (n : ℕ) :
    {i | ¬ IsZero (groupCohomology (ideleIntegralBlock wf wi i) (n + 1))}.Finite := by
  refine ((finite_setOf_ramified_wf wf).image Sum.inl |>.union
    (Set.finite_range (Sum.inr : InfinitePlace F → _))).subset ?_
  rintro (v | v) hv
  · refine Or.inl ⟨v, fun he => hv ?_, rfl⟩
    exact isZero_groupCohomology_coindLocalUnits v (wf v) he n
  · exact Or.inr ⟨v, rfl⟩

include hwi in
/-- **Finite support.** Only finitely many finite local components of a class of
`Hⁿ⁺¹(Gal(E/F), J_E)` are nonzero. -/
theorem finite_ideleLocalMap_ne_zero (n : ℕ) (x : relativeIdeleCohomology F E (n + 1)) :
    {v | ideleLocalMap v (wf v) (n + 1) x ≠ 0}.Finite := by
  refine (((isRestrictedProduct_ideleBlock wf wi hwi).finite_map_ne_zero n
    (finite_not_isZero_ideleIntegralBlock wf wi n) x).preimage Sum.inl_injective.injOn).subset ?_
  intro v hv h0
  apply hv
  rw [ideleLocalMap_eq, ConcreteCategory.comp_apply]
  change Shapiro.shapiroMapOf _ _ (n + 1) _ = 0
  rw [show groupCohomology.map (MonoidHom.id _) (ideleSemilocalProjection v (wf v)) (n + 1) x = 0
    from h0, map_zero]

include hwi in
/-- **Local triviality of idèle cohomology.** A class of `Hⁿ⁺¹(Gal(E/F), J_E)` whose local
components at the chosen places above all places of `F` vanish is zero. -/
theorem eq_zero_of_ideleLocalMap_eq_zero (n : ℕ) (x : relativeIdeleCohomology F E (n + 1))
    (hfin : ∀ v, ideleLocalMap v (wf v) (n + 1) x = 0)
    (hinf : ∀ v, ideleInfiniteLocalMap (wi v) (n + 1) x = 0) : x = 0 := by
  refine (isRestrictedProduct_ideleBlock wf wi hwi).eq_zero_of_map_eq_zero n
    (finite_not_isZero_ideleIntegralBlock wf wi n) x ?_
  rintro (v | v)
  · exact map_ideleSemilocalProjection_eq_zero v (wf v) (n + 1) x (hfin v)
  · exact map_infiniteSemilocalProjection_eq_zero (wi v) (n + 1) x (hinf v)

end Injectivity

section InfiniteSection

variable (w : InfinitePlace E)
  [Fintype ((E ≃ₐ[F] E) ⧸ (MulAction.stabilizer (E ≃ₐ[F] E) w).subtype.range)]

/-- A section of the local map `Hⁿ(Gal(E/F), J_E) → Hⁿ(D_w, E_wˣ)` at an infinite place: the
inverse Shapiro isomorphism followed by the map induced by the semilocal section. -/
def ideleInfiniteLocalSection (n : ℕ) :
    groupCohomology (infiniteLocalRepresentation F w) n ⟶ relativeIdeleCohomology F E n :=
  (Shapiro.shapiroIsoOf (Subgroup.subtype_injective _) _ n).inv ≫
    groupCohomology.map (MonoidHom.id _) (infiniteSemilocalSection F w) n

omit [NumberField F] [IsGalois F E] in
/-- The infinite local map is a split epimorphism. -/
@[reassoc (attr := simp)]
theorem ideleInfiniteLocalSection_comp_ideleInfiniteLocalMap (n : ℕ) :
    ideleInfiniteLocalSection (F := F) w n ≫ ideleInfiniteLocalMap (F := F) w n = 𝟙 _ := by
  rw [ideleInfiniteLocalMap, ← map_infiniteSemilocalProjection_comp_shapiroMapOf,
    ideleInfiniteLocalSection, Category.assoc, ← groupCohomology.map_id_comp_assoc,
    infiniteSemilocalSection_comp_infiniteSemilocalProjection, groupCohomology.map_id,
    Category.id_comp, ← Shapiro.shapiroIsoOf_hom (Subgroup.subtype_injective _), Iso.inv_hom_id]

omit [NumberField F] [IsGalois F E] in
/-- The semilocal section at `w`, followed by the coordinate at `w'`, is zero when no element of
`Gal(E/F)` moves `w'` to `w`. -/
theorem infiniteSemilocalSection_comp_infiniteLocalProjection_of_ne (w' : InfinitePlace E)
    (h : ∀ g : E ≃ₐ[F] E, infinitePlaceEquiv g.toRingEquiv w' ≠ w) :
    (Rep.resFunctor (MulAction.stabilizer (E ≃ₐ[F] E) w').subtype).map
        (infiniteSemilocalSection F w) ≫ infiniteLocalProjection F w' = 0 := by
  ext f
  change infiniteCoordinateLinear F w' ((infiniteSemilocalSection F w).hom f) = 0
  rw [infiniteSemilocalSection, Shapiro.coindSum_hom_apply, map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  induction c using QuotientGroup.induction_on with | H x => ?_
  exact congrArg Additive.ofMul
    (ideleInfiniteCoordinate_relativeIdeleAut_ofCompletion_of_ne x (h x) _)

omit [NumberField F] [IsGalois F E] in
/-- **Orthogonality** of the infinite local sections and maps at places in different orbits. -/
theorem ideleInfiniteLocalSection_comp_ideleInfiniteLocalMap_of_ne (w' : InfinitePlace E)
    (h : ∀ g : E ≃ₐ[F] E, infinitePlaceEquiv g.toRingEquiv w' ≠ w) (n : ℕ) :
    ideleInfiniteLocalSection (F := F) w n ≫ ideleInfiniteLocalMap (F := F) w' n = 0 := by
  rw [ideleInfiniteLocalSection, Category.assoc, ideleInfiniteLocalMap, ← groupCohomology.map_comp,
    infiniteSemilocalSection_comp_infiniteLocalProjection_of_ne w w' h, groupCohomology.map,
    groupCohomology.cochainsMap_zero, HomologicalComplex.homologyMap_zero]
  exact Limits.comp_zero

end InfiniteSection

end

end Langlands.GaloisCohomology
