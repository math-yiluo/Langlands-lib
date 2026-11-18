import Langlands.Geometry.Analytic.AffineAnalytificationLocalDomainMaps
import Langlands.Geometry.Analytic.AnalytificationCenter
import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumIdealCriterionProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLaurentNeighborhoods
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain

/-! # Scheme morphisms from spectra of affinoid algebras into a scheme -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification.AffinoidPoints

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification

section Algebraic

variable {K : Type u} [CommRing K] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of K)}

/-- A `K`-algebra map out of the global sections of an affine open `U`, as a morphism of
commutative rings with source `Γ(U, ⊤)`. -/
def coordHom (U : X.affineOpens) {R : Type u} [CommRing R] [Algebra K R]
    (α : CoordinateRing (structureMap f U) →ₐ[K] R) :
    Γ((U : X.Opens), ⊤) ⟶ CommRingCat.of R :=
  CommRingCat.ofHom α.toRingHom

/-- The structure map `K → Γ(U, ⊤)` of the global sections of an affine open `U`. -/
def baseHom (f : X ⟶ Spec (CommRingCat.of K)) (U : X.affineOpens) :
    CommRingCat.of K ⟶ Γ((U : X.Opens), ⊤) :=
  CommRingCat.ofHom (algebraMap K (CoordinateRing (structureMap f U)))

/-- The morphism `Spec R → X` given by a `K`-algebra map from the global sections of an
affine open `U` to `R`: the morphism of spectra followed by `Spec Γ(U, ⊤) ≅ U ⊆ X`. -/
def schemePoint (U : X.affineOpens) {R : Type u} [CommRing R] [Algebra K R]
    (α : CoordinateRing (structureMap f U) →ₐ[K] R) : Spec (CommRingCat.of R) ⟶ X :=
  Spec.map (coordHom U α) ≫ affineOpenMap U

theorem schemePoint_comp (U : X.affineOpens) {R R' : Type u} [CommRing R] [Algebra K R]
    [CommRing R'] [Algebra K R'] (α : CoordinateRing (structureMap f U) →ₐ[K] R)
    (ψ : R →ₐ[K] R') :
    schemePoint U (ψ.comp α) =
      Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ schemePoint U α := by
  rw [schemePoint, schemePoint, ← Category.assoc, ← Spec.map_comp]
  rfl

instance (U : X.affineOpens) : Mono (affineOpenMap U) := by
  rw [affineOpenMap]
  infer_instance

/-- A `K`-algebra map out of the global sections of an affine open is determined by its
scheme morphism. -/
theorem schemePoint_injective (U : X.affineOpens) {R : Type u} [CommRing R] [Algebra K R]
    {α β : CoordinateRing (structureMap f U) →ₐ[K] R}
    (h : schemePoint U α = schemePoint U β) : α = β := by
  have h1 := Spec.map_injective ((cancel_mono (affineOpenMap U)).1 h)
  exact AlgHom.ext fun a => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h1) a

theorem affineOpenMap_restriction {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) :
    Spec.map (X.homOfLE h).appTop ≫ affineOpenMap U = affineOpenMap V := by
  rw [affineOpenMap, affineOpenMap, Scheme.isoSpec_inv_naturality_assoc, X.homOfLE_ι]

/-- Precomposition with the restriction of global sections to a smaller affine open. -/
theorem schemePoint_restriction {U V : X.affineOpens} (h : (V : X.Opens) ≤ U)
    {R : Type u} [CommRing R] [Algebra K R]
    (γ : CoordinateRing (structureMap f V) →ₐ[K] R) :
    schemePoint U (γ.comp (restriction f h)) = schemePoint V γ := by
  rw [schemePoint, schemePoint, ← affineOpenMap_restriction h, ← Category.assoc,
    ← Spec.map_comp]
  rfl

theorem isoSpec_hom_baseHom (U : X.affineOpens) :
    (U : X.Opens).toScheme.isoSpec.hom ≫ Spec.map (baseHom f U) = structureMap f U :=
  coordinateIso_hom_over (structureMap f U)

theorem affineOpenMap_over (U : X.affineOpens) :
    affineOpenMap U ≫ f = Spec.map (baseHom f U) := by
  rw [affineOpenMap, Category.assoc]
  change (U : X.Opens).toScheme.isoSpec.inv ≫ structureMap f U = _
  rw [← isoSpec_hom_baseHom, Iso.inv_hom_id_assoc]

theorem baseHom_comp_coordHom (U : X.affineOpens) {R : Type u} [CommRing R] [Algebra K R]
    (α : CoordinateRing (structureMap f U) →ₐ[K] R) :
    baseHom f U ≫ coordHom U α = CommRingCat.ofHom (algebraMap K R) := by
  ext k
  exact α.commutes k

/-- The scheme morphism lies over `Spec K`. -/
theorem schemePoint_over (U : X.affineOpens) {R : Type u} [CommRing R] [Algebra K R]
    (α : CoordinateRing (structureMap f U) →ₐ[K] R) :
    schemePoint U α ≫ f = Spec.algebraMap K R := by
  rw [schemePoint, Category.assoc, affineOpenMap_over, ← Spec.map_comp,
    baseHom_comp_coordHom]

/-- A scheme morphism of the form `schemePoint U α` whose image lies in another affine open
`U'` has the form `schemePoint U' α'`. -/
theorem exists_schemePoint_eq (U U' : X.affineOpens) {R : Type u} [CommRing R] [Algebra K R]
    (α : CoordinateRing (structureMap f U) →ₐ[K] R)
    (h : Set.range (schemePoint U α) ⊆ ((U' : X.Opens) : Set X)) :
    ∃ α' : CoordinateRing (structureMap f U') →ₐ[K] R, schemePoint U' α' = schemePoint U α := by
  have hr : Set.range (schemePoint U α) ⊆ Set.range (U' : X.Opens).ι := by
    rw [Scheme.Opens.range_ι]
    exact h
  obtain ⟨φ, hφ⟩ := Spec.map_surjective
    (IsOpenImmersion.lift (U' : X.Opens).ι (schemePoint U α) hr ≫
      (U' : X.Opens).toScheme.isoSpec.hom)
  have hsp : Spec.map φ ≫ affineOpenMap U' = schemePoint U α := by
    rw [hφ, affineOpenMap, Category.assoc, Iso.hom_inv_id_assoc, IsOpenImmersion.lift_fac]
  have e : Spec.map φ ≫ Spec.map (baseHom f U') = Spec.algebraMap K R := by
    rw [← affineOpenMap_over, ← Category.assoc, hsp, schemePoint_over]
  rw [Spec.algebraMap, ← Spec.map_comp] at e
  have e2 := Spec.map_injective e
  refine ⟨{ toRingHom := φ.hom,
             commutes' := fun k => DFunLike.congr_fun (congrArg CommRingCat.Hom.hom e2) k }, ?_⟩
  exact hsp

end Algebraic

section Affinoid

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

open AffineAnalytification AffineAnalytification.LocalDomainMaps

theorem localCenter_mem (U : X.affineOpens) (y : LocalSpace K f U) :
    localCenter K f U y ∈ (U : X.Opens) :=
  center_ι_mem K f U y

/-- The kernel of a spectrum point of `R`, as a point of `Spec R`. -/
def kernelPoint {R : PresentedAffinoidAlgebra K} (x : BanachSpectrum R) :
    Spec (CommRingCat.of R) :=
  (⟨x.kernel, x.kernel_isPrime⟩ : PrimeSpectrum R)

/-- The kernel point of a spectrum point is sent to the center of its image in the
analytification. -/
theorem schemePoint_kernel (U : X.affineOpens) {R : PresentedAffinoidAlgebra K}
    (α : CoordinateRing (structureMap f U) →ₐ[K] R) (x : BanachSpectrum R) :
    schemePoint U α (kernelPoint K x) =
      localCenter K f U (affinoidBaseMap K (chartPresentation K f U) R α x) := by
  rw [localCenter_apply, schemePoint, Scheme.Hom.comp_apply]
  congr 1
  apply PrimeSpectrum.ext
  exact (kernel_affinoidBaseMap (chartPresentation K f U) R α x).symm

/-- If the centers of all images of spectrum points lie in an open subset, so does the
entire image of the scheme morphism: every prime ideal of an affinoid algebra lies in the
kernel of a spectrum point. -/
theorem range_schemePoint_subset (U : X.affineOpens) {R : PresentedAffinoidAlgebra K}
    (α : CoordinateRing (structureMap f U) →ₐ[K] R) (O : X.Opens)
    (h : ∀ x : BanachSpectrum R,
      localCenter K f U (affinoidBaseMap K (chartPresentation K f U) R α x) ∈ O) :
    Set.range (schemePoint U α) ⊆ (O : Set X) := by
  rintro _ ⟨p, rfl⟩
  obtain ⟨x, hx⟩ := PresentedAffinoidAlgebra.exists_spectrum_kernel_of_proper_ideal R
    (p : PrimeSpectrum R).asIdeal (p : PrimeSpectrum R).isPrime.ne_top
  have hs : p ⤳ kernelPoint K x :=
    (PrimeSpectrum.le_iff_specializes (p : PrimeSpectrum R)
      (⟨x.kernel, x.kernel_isPrime⟩ : PrimeSpectrum R)).mp hx
  have hmem := h x
  rw [← schemePoint_kernel] at hmem
  exact (hs.map (schemePoint U α).continuous).mem_open O.isOpen hmem

/-- Two scheme morphisms `Spec R → X` of the form `schemePoint` that agree give the same
point of the glued analytification at every spectrum point of `R`. -/
theorem ι_affinoidBaseMap_eq {U U' : X.affineOpens} {R : PresentedAffinoidAlgebra K}
    (α : CoordinateRing (structureMap f U) →ₐ[K] R)
    (α' : CoordinateRing (structureMap f U') →ₐ[K] R)
    (h : schemePoint U α = schemePoint U' α') (x : BanachSpectrum R) :
    ι K f U (affinoidBaseMap K (chartPresentation K f U) R α x) =
      ι K f U' (affinoidBaseMap K (chartPresentation K f U') R α' x) := by
  let p := kernelPoint K x
  have hpU : schemePoint U α p ∈ (U : X.Opens) := by
    rw [schemePoint_kernel]
    exact localCenter_mem K f U _
  have hpU' : schemePoint U α p ∈ (U' : X.Opens) := by
    rw [h, schemePoint_kernel]
    exact localCenter_mem K f U' _
  obtain ⟨_, ⟨W, hW, rfl⟩, hpW, hWUU'⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show schemePoint U α p ∈ (((U : X.Opens) ⊓ (U' : X.Opens) : X.Opens) : Set X) from
      ⟨hpU, hpU'⟩) ((U : X.Opens) ⊓ (U' : X.Opens)).isOpen
  let W' : X.affineOpens := ⟨W, hW⟩
  have hWU : (W'.1 : X.Opens) ≤ U := fun z hz => (hWUU' hz).1
  have hWU' : (W'.1 : X.Opens) ≤ U' := fun z hz => (hWUU' hz).2
  obtain ⟨_, ⟨g, rfl⟩, hpg, hgO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ (schemePoint U α) ⁻¹' (W : Set X) from hpW)
      (W.isOpen.preimage (schemePoint U α).continuous)
  have hxg : x g ≠ 0 := hpg
  let V : Set (BanachSpectrum R) := {y | y g ≠ 0}
  have hV : IsOpen V :=
    isOpen_ne_fun (BanachSpectrum.evaluation g).continuous continuous_const
  obtain ⟨d, hd, hdV⟩ := PresentedAffinoidAlgebra.RationalChart.exists_rational_neighborhood x V
    (hV.mem_nhds hxg)
  let D := d.toDomain
  let ρ := D.baseMap
  have hunit : IsUnit (ρ g) :=
    (PresentedAffinoidAlgebra.isUnit_iff_forall_spectrum_ne_zero D.algebra (ρ g)).2
      (fun y => hdV (D.represents.hasImageIn y))
  have hrange : Set.range (schemePoint U (ρ.toAlgHom.comp α)) ⊆ ((W'.1 : X.Opens) : Set X) := by
    rintro _ ⟨q, rfl⟩
    rw [schemePoint_comp, Scheme.Hom.comp_apply]
    apply hgO
    change g ∉ (PrimeSpectrum.comap ρ.toRingHom (q : PrimeSpectrum D.algebra)).asIdeal
    intro hq
    exact (q : PrimeSpectrum D.algebra).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hq hunit)
  obtain ⟨γ, hγ⟩ := exists_schemePoint_eq U W' (ρ.toAlgHom.comp α) hrange
  have hγU : γ.comp (restriction f hWU) = ρ.toAlgHom.comp α :=
    schemePoint_injective U (by rw [schemePoint_restriction, hγ])
  have hγU' : γ.comp (restriction f hWU') = ρ.toAlgHom.comp α' :=
    schemePoint_injective U' (by
      rw [schemePoint_restriction, hγ, schemePoint_comp, schemePoint_comp, h])
  obtain ⟨x', rfl⟩ : x ∈ Set.range (BanachSpectrum.comap ρ.toBoundedRingHom) := by
    rw [D.represents.2.1]
    exact mem_of_mem_nhds hd
  have key : ∀ {U₀ : X.affineOpens} (hW₀ : (W'.1 : X.Opens) ≤ U₀)
      (β : CoordinateRing (structureMap f U₀) →ₐ[K] R)
      (_ : γ.comp (restriction f hW₀) = ρ.toAlgHom.comp β),
      ι K f U₀ (affinoidBaseMap K (chartPresentation K f U₀) R β
          (BanachSpectrum.comap ρ.toBoundedRingHom x')) =
        ι K f W' (affinoidBaseMap K (chartPresentation K f W') D.algebra γ x') := by
    intro U₀ hW₀ β hβ
    rw [← affinoidBaseMap_comp_left, ← hβ, ← baseMap_affinoidBaseMap]
    exact ι_localMap K f hW₀ _
  rw [key hWU α hγU, key hWU' α' hγU']

end Affinoid

end Langlands.Analytic.SchemeAnalytification.AffinoidPoints
