import Langlands.Geometry.Analytic.AffineAnalytificationFinitePieceLocalStatement
import Langlands.Geometry.Analytic.AffineAnalytificationFiniteGermComparisonStatement
import Langlands.Geometry.Analytic.TensorStalkReflection
import Langlands.Geometry.Analytic.AffineAnalytificationSeminorm

/-! # The finite-germ comparison from the local structure of the finite pieces -/

noncomputable section

universe u v w z

namespace Langlands.Analytic

open scoped TensorProduct Topology
open TensorProduct

namespace TensorStalkBaseChange

section Reflection

variable {R : Type u} {S : Type v} {T : Type w} {D : Type z}
  [CommRing R] [CommRing S] [CommRing T] [CommRing D]
  [Algebra R S] [Algebra R T] [Algebra R D] [Algebra S D] [Algebra T D]
  [IsScalarTower R S D] [IsScalarTower R T D]
  [Algebra.IsPushout R T S D]

omit [Algebra.IsPushout R T S D] in
/-- In an algebraic pushout with flat horizontal maps, flatness at a target prime
reflects to the corresponding prime of the original algebra. -/
theorem flat_atPrime_reflect [Module.Flat R T] [Module.Flat S D]
    (p : Ideal D) [p.IsPrime]
    (hflat : Module.Flat T (Localization.AtPrime p)) :
    Module.Flat R (Localization.AtPrime (p.comap (algebraMap S D))) := by
  let q := p.comap (algebraMap S D)
  let M := Localization.AtPrime q
  let L := Localization.AtPrime p
  let : Algebra M L :=
    (Localization.localRingHom q p (algebraMap S D) rfl).toAlgebra
  have : IsScalarTower S M L := .of_algebraMap_eq fun s =>
    (Localization.localRingHom_to_map q p (algebraMap S D) rfl s).symm
  have : IsScalarTower R M L := IsScalarTower.to₁₃₄ R S M L
  have hf : (algebraMap S D).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Module.Flat M L := hf.localRingHom p q rfl
  have : Module.FaithfullyFlat M L := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Module.Flat T L := hflat
  have : Module.Flat R L := Module.Flat.trans R T L
  exact flat_of_faithfullyFlat_target R M L

/-- In an algebraic pushout whose right vertical map is flat, formal unramifiedness at
a target prime reflects to the corresponding prime of the original algebra. -/
theorem formallyUnramified_atPrime_reflect [Module.Flat S D]
    (p : Ideal D) [p.IsPrime]
    (hunr : Algebra.FormallyUnramified T (Localization.AtPrime p)) :
    Algebra.FormallyUnramified R (Localization.AtPrime (p.comap (algebraMap S D))) := by
  let q := p.comap (algebraMap S D)
  let M := Localization.AtPrime q
  let L := Localization.AtPrime p
  let : Algebra M L :=
    (Localization.localRingHom q p (algebraMap S D) rfl).toAlgebra
  have : IsScalarTower S M L := .of_algebraMap_eq fun s =>
    (Localization.localRingHom_to_map q p (algebraMap S D) rfl s).symm
  have : IsScalarTower R M L := IsScalarTower.to₁₃₄ R S M L
  have hf : (algebraMap S D).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Module.Flat M L := hf.localRingHom p q rfl
  have : Module.FaithfullyFlat M L := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : Algebra.FormallyUnramified T L := hunr
  have : Subsingleton Ω[L⁄T] := inferInstance
  have : Algebra.FormallyEtale D L :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  have : Algebra.FormallyEtale S M :=
    Algebra.FormallyEtale.of_isLocalization q.primeCompl
  let eL := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale T D L
  have : Subsingleton (L ⊗[D] Ω[D⁄T]) := eL.injective.subsingleton
  let eBase := KaehlerDifferential.tensorKaehlerEquiv R T S D
  have : Subsingleton (L ⊗[D] (D ⊗[S] Ω[S⁄R])) :=
    (eBase.lTensor L).injective.subsingleton
  have : Subsingleton (L ⊗[S] Ω[S⁄R]) :=
    (AlgebraTensorModule.cancelBaseChange S D D L Ω[S⁄R]).symm.injective.subsingleton
  have : Subsingleton (L ⊗[M] (M ⊗[S] Ω[S⁄R])) :=
    (AlgebraTensorModule.cancelBaseChange S M M L Ω[S⁄R]).injective.subsingleton
  let eM := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S M
  have : Subsingleton (L ⊗[M] Ω[M⁄R]) :=
    (eM.symm.lTensor L).injective.subsingleton
  have : Subsingleton Ω[M⁄R] :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right M L
      (N := Ω[M⁄R])).mp inferInstance
  exact (Algebra.formallyUnramified_iff R M).mpr this

end Reflection

section LocalComparison

variable {A : Type u} {B : Type v} {R : Type w} {S : Type z}
  [CommRing A] [CommRing B] [CommRing R] [CommRing S]

/-- Flatness of the local map `A_{f⁻¹ q} → B_q` is flatness of `B_q` over `A`. -/
theorem localRingHom_flat_iff (f : A →+* B) (q : Ideal B) [q.IsPrime] :
    (Localization.localRingHom (q.comap f) q f rfl).Flat ↔
      (letI : Algebra A B := f.toAlgebra
       Module.Flat A (Localization.AtPrime q)) := by
  let : Algebra A B := f.toAlgebra
  let p := q.comap f
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q f rfl).toAlgebra
  have : IsScalarTower A (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_algebraMap_eq fun x => (Localization.localRingHom_to_map p q f rfl x).symm
  change Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) ↔ _
  exact Module.flat_iff_of_isLocalization
    (S := Localization.AtPrime p) (p := p.primeCompl) (Localization.AtPrime q)

/-- A ring map `χ : C → S` of `R`-algebras whose localization at the primes of `𝔰`
is bijective gives an `R`-algebra equivalence of these localizations. -/
def localAlgEquivOfBijective {C : Type*} [CommRing C] [Algebra R C] [Algebra R S]
    (χ : C →+* S) (hχ : ∀ r : R, χ (algebraMap R C r) = algebraMap R S r)
    (𝔰 : Ideal S) [𝔰.IsPrime]
    (hbij : Function.Bijective (Localization.localRingHom (𝔰.comap χ) 𝔰 χ rfl)) :
    Localization.AtPrime (𝔰.comap χ) ≃ₐ[R] Localization.AtPrime 𝔰 :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _ hbij) fun r => by
    change Localization.localRingHom (𝔰.comap χ) 𝔰 χ rfl
      (algebraMap R (Localization.AtPrime (𝔰.comap χ)) r) = _
    rw [IsScalarTower.algebraMap_apply R C (Localization.AtPrime (𝔰.comap χ)),
      Localization.localRingHom_to_map, hχ,
      ← IsScalarTower.algebraMap_apply R S (Localization.AtPrime 𝔰)]

/-- The algebraic core of the finite-germ comparison: let `R` be a flat `A`-algebra,
`φ : R → S` a ring map and `χ : R ⊗[A] B → S` a ring map extending `φ`, whose
localization at the prime of `𝔰` is bijective. Then for the prime `q` of `B` under `𝔰`,
`S_𝔰` is flat (respectively formally unramified) over `R` if and only if `B_q` is flat
(respectively formally unramified) over `A`. -/
theorem flat_and_formallyUnramified_iff_of_localBijective
    [Algebra A B] [Algebra A R] [Module.Flat A R]
    (φ : R →+* S) (χ : R ⊗[A] B →+* S) (hχ : ∀ r : R, χ (r ⊗ₜ[A] 1) = φ r)
    (𝔰 : Ideal S) [𝔰.IsPrime]
    (hbij : Function.Bijective (Localization.localRingHom (𝔰.comap χ) 𝔰 χ rfl))
    (q : Ideal B) [q.IsPrime]
    (hq : q = (𝔰.comap χ).comap
      (Algebra.TensorProduct.includeRight (R := A) (A := R) (B := B)).toRingHom) :
    ((letI : Algebra R S := φ.toAlgebra
      Module.Flat R (Localization.AtPrime 𝔰)) ↔ Module.Flat A (Localization.AtPrime q)) ∧
    ((letI : Algebra R S := φ.toAlgebra
      Algebra.FormallyUnramified R (Localization.AtPrime 𝔰)) ↔
        Algebra.FormallyUnramified A (Localization.AtPrime q)) := by
  subst hq
  let : Algebra R S := φ.toAlgebra
  let 𝔠 : Ideal (R ⊗[A] B) := 𝔰.comap χ
  let e : Localization.AtPrime 𝔠 ≃ₐ[R] Localization.AtPrime 𝔰 :=
    localAlgEquivOfBijective χ (fun r => hχ r) 𝔰 hbij
  let _ : Algebra B (R ⊗[A] B) := Algebra.TensorProduct.rightAlgebra (R := A) (A := R) (B := B)
  have : Module.Flat B (R ⊗[A] B) :=
    Module.Flat.isBaseChange A B R (R ⊗[A] B)
      (TensorProduct.isPushout' (R := A) (S := R) (T := B)).out
  refine ⟨⟨fun hS => ?_, fun hB => ?_⟩, ⟨fun hS => ?_, fun hB => ?_⟩⟩
  · have : Module.Flat R (Localization.AtPrime 𝔠) :=
      Module.Flat.of_linearEquiv e.toLinearEquiv
    exact flat_atPrime_reflect (R := A) (T := R) (S := B) (D := R ⊗[A] B) 𝔠 this
  · have : Module.Flat R (Localization.AtPrime 𝔠) := flat_atPrime (R := A) (S := B) (T := R) 𝔠 hB
    exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  · have : Algebra.FormallyUnramified R (Localization.AtPrime 𝔠) :=
      Algebra.FormallyUnramified.of_equiv e.symm
    exact formallyUnramified_atPrime_reflect (R := A) (T := R) (S := B) (D := R ⊗[A] B) 𝔠 this
  · have : Algebra.FormallyUnramified R (Localization.AtPrime 𝔠) :=
      formallyUnramified_atPrime (R := A) (S := B) (T := R) 𝔠 hB
    exact Algebra.FormallyUnramified.of_equiv e

end LocalComparison

end TensorStalkBaseChange

namespace AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- At a point where `g` is finite, a property with finite pieces is equivalent to a
proposition `Pr` as soon as every finite piece satisfies the pointwise property at every
point over `y` exactly when `Pr` holds. -/
theorem hasFinitePiecesAt_iff_of_pieces
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄, BoundedAlgHom K R S → BanachSpectrum S → Prop}
    {g : StrongHom A.saturatedPresentation B.saturatedPresentation} {y : A.space}
    (hfin : g.IsFiniteAt y) (Pr : Prop)
    (hpiece : ∀ (V : Set A.space) (U : Set B.space), IsOpen V → IsOpen U →
      g.IsFiniteOver V U →
      ∀ W : B.atlas.saturatedAtlas.RecognizedSubset, W.locus ⊆ U →
      ∀ (V' : A.atlas.saturatedAtlas.RecognizedSubset)
        (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart),
        V'.locus = V ∩ g.baseMap ⁻¹' W.locus →
          ∀ s : BanachSpectrum V'.algebra, V'.chart s = y →
            (Q (g.fullRecognitionPairs.pullback V' W h) s ↔ Pr)) :
    g.HasFinitePiecesAt Q y ↔ Pr := by
  constructor
  · rintro ⟨V, U, hV, hU, hy, hVU, I, -, hIU, hIN, hIQ⟩
    obtain ⟨W, hW, hyW⟩ := Set.mem_iUnion₂.mp (mem_of_mem_nhds hIN)
    obtain ⟨V', h, hV', -⟩ := hVU.2 W (hIU W hW).1
    have hyV' : y ∈ Set.range V'.chart := by
      rw [V'.range_chart, hV']
      exact ⟨hy, hyW⟩
    obtain ⟨s, hs⟩ := hyV'
    exact (hpiece V U hV hU hVU W (hIU W hW).1 V' h hV' s hs).1 (hIQ W hW V' h hV' s hs)
  · intro hPr
    obtain ⟨V, U, hV, hU, hy, hVU⟩ := hfin
    have hUy : U ∈ 𝓝 (g.baseMap y) := hU.mem_nhds (hVU.1 ⟨y, hy, rfl⟩)
    obtain ⟨I, hI, hIU, hIN⟩ :=
      B.atlas.exists_finite_recognized_nhds_subset (g.baseMap y) U hUy
    exact ⟨V, U, hV, hU, hy, hVU, I, hI, fun W hW => ⟨(hIU W hW).2, (hIU W hW).1⟩, hIN,
      fun W hW V' h hV' s hs => (hpiece V U hV hU hVU W (hIU W hW).2 V' h hV' s hs).2 hPr⟩

end AffinoidAtlasPresentation.StrongHom

namespace AffineAnalytification

open AffinoidAtlasPresentation

/-- On one finite piece of `g := saturatedHom K P Q f` over a point `y` of the `m`-th
chart, the local structure statement makes pointwise flatness and unramifiedness of the
piece equivalent to flatness of `B_q` over `A` and unramifiedness of `f` at `q`. -/
theorem finitePiece_iff (H : AffineAnalytificationFinitePieceLocalStatement.{u, v, w})
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : Type v) [CommRing A] [Algebra K A] (B : Type w) [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B) (m : ℕ) (s : BanachSpectrum (algebra K Q m))
    (V : Set (presentation K Q).space) (U : Set (presentation K P).space)
    (hV : IsOpen V) (hU : IsOpen U)
    (hVU : StrongHom.IsFiniteOver (A := presentation K Q) (B := presentation K P)
      (saturatedHom K P Q f) V U)
    (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset) (hWU : W.locus ⊆ U)
    (V' : (presentation K Q).atlas.saturatedAtlas.RecognizedSubset)
    (h : (saturatedHom K P Q f).baseMap '' Set.range V'.chart ⊆ Set.range W.chart)
    (hV' : V'.locus = V ∩ (saturatedHom K P Q f).baseMap ⁻¹' W.locus)
    (s' : BanachSpectrum V'.algebra) (hs' : V'.chart s' = chart K Q m s) :
    let q := s.kernel.comap
      (PolynomialLocus.algebraMap Q (AnalyticAffineSpace.polyradius K Q.arity m)).toRingHom
    (((saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h).IsFlatAtPoint s' ↔
        (letI : Algebra A B := f.toRingHom.toAlgebra
         Module.Flat A (Localization.AtPrime q))) ∧
      (((saturatedHom K P Q f).fullRecognitionPairs.pullback V' W h).IsUnramifiedAtPoint s' ↔
        (letI : Algebra A B := f.toRingHom.toAlgebra
         Algebra.IsUnramifiedAt A q)) := by
  intro q
  -- The piece is finite: `V'` is the recognized subset given by finiteness over `W`.
  obtain ⟨V'', h'', hV'', hfinB⟩ := hVU.2 W hWU
  have hVV : V'' = V' := Subtype.ext (Subtype.ext (hV''.trans hV'.symm))
  subst hVV
  obtain ⟨α, β, hα, -, hβ, χ, hχ₁, hχ₂, hloc⟩ :=
    H K A B P Q f V U hV hU hVU W hWU V'' h hV' hfinB
  let : Algebra A W.algebra := α.toRingHom.toAlgebra
  let : Algebra A B := f.toRingHom.toAlgebra
  have : Module.Flat A W.algebra := hα
  let φ : BoundedAlgHom K W.algebra V''.algebra :=
    (saturatedHom K P Q f).fullRecognitionPairs.pullback V'' W h
  -- The prime of `B` under `s'` is the prime `q` of the point `y`.
  have hq : q = (s'.kernel.comap χ).comap
      (Algebra.TensorProduct.includeRight (R := A) (A := W.algebra) (B := B)).toRingHom := by
    ext b
    change s (PolynomialLocus.algebraMap Q (AnalyticAffineSpace.polyradius K Q.arity m) b) = 0 ↔
      s' (χ (1 ⊗ₜ[A] b)) = 0
    rw [hχ₂, hβ, hs', pointSeminorm_chart, chartSeminorm_apply]
  have core := TensorStalkBaseChange.flat_and_formallyUnramified_iff_of_localBijective
    φ.toAlgHom.toRingHom χ (fun r => hχ₁ r) s'.kernel (hloc s') q hq
  have hft : φ.toAlgHom.toRingHom.FiniteType := hfinB.finite.finiteType
  exact ⟨(BoundedAlgHom.isFlatAtPoint_iff_flat_atPrime φ s').trans core.1,
    (BoundedAlgHom.isUnramifiedAtPoint_iff_isUnramifiedAt φ hft s').trans core.2⟩

/-- The finite-germ comparison follows from the local structure statement for the finite
pieces of the affine analytification map. -/
theorem finiteGermComparison_of_finitePieceLocal
    (H : AffineAnalytificationFinitePieceLocalStatement.{u, v, w}) :
    AffineAnalytificationFiniteGermComparisonStatement.{u, v, w} := by
  intro K _ _ _ A _ _ B _ _ P Q f m s g y q hfin
  have key := fun (V : Set (presentation K Q).space) (U : Set (presentation K P).space)
      (hV : IsOpen V) (hU : IsOpen U)
      (hVU : StrongHom.IsFiniteOver (A := presentation K Q) (B := presentation K P) g V U)
      (W : (presentation K P).atlas.saturatedAtlas.RecognizedSubset) (hWU : W.locus ⊆ U)
      (V' : (presentation K Q).atlas.saturatedAtlas.RecognizedSubset)
      (h : g.baseMap '' Set.range V'.chart ⊆ Set.range W.chart)
      (hV' : V'.locus = V ∩ g.baseMap ⁻¹' W.locus)
      (s' : BanachSpectrum V'.algebra) (hs' : V'.chart s' = y) =>
    finitePiece_iff H K A B P Q f m s V U hV hU hVU W hWU V' h hV' s' hs'
  refine ⟨StrongHom.hasFinitePiecesAt_iff_of_pieces hfin _
      fun V U hV hU hVU W hWU V' h hV' s' hs' => (key V U hV hU hVU W hWU V' h hV' s' hs').2,
    ?_⟩
  rw [TensorStalkBaseChange.localRingHom_flat_iff]
  exact StrongHom.hasFinitePiecesAt_iff_of_pieces hfin _
    fun V U hV hU hVU W hWU V' h hV' s' hs' => (key V U hV hU hVU W hWU V' h hV' s' hs').1

end AffineAnalytification

end Langlands.Analytic
