import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsEqualizer
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsAlgebra

/-! # Shrinking a chart of Murre's construction

Fix a point `s` of `Spec R`, a representation `e` of the base change of `F` to
`Spec 𝒪_{Spec R, s}` by `Y`, and an open immersion `j : Spec B ⟶ Y`, giving `ξ_B ∈ F(Spec B)`.
Let `A` be an `R`-algebra with `B = M⁻¹A` and `ξ ∈ F(Spec A)` restricting to `ξ_B`. This module
shows that for suitable `b ∈ M` the restriction of `ξ` to `Spec A[1/b]` is formally
unramified, infinitesimally étale at every point (given that the étale locus of such
restrictions is open, Murre's Lemma 2) and a monomorphism. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section Restrict

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The restriction of `ξ ∈ F(Spec A)` to `Spec A[1/a]`. -/
abbrev resA (ξ : F.obj (op (ovR R A))) (a : A) : F.obj (op (ovR R (Localization.Away a))) :=
  F.map (homR (IsScalarTower.toAlgHom R A (Localization.Away a))).op ξ

lemma resA_awayMapₐ (ξ : F.obj (op (ovR R A))) {a b : A} (h : a ∣ b) :
    F.map (homR (awayMapₐ (R := R) h)).op (resA ξ a) = resA ξ b := by
  rw [resA, map_homR_map_homR, awayMapₐ_comp_toAlgHom]

lemma unit_of_dvd {b n : A} (hn : n ∣ b) :
    IsUnit (algebraMap A (Localization.Away b) n) :=
  isUnit_of_dvd_unit (map_dvd _ hn) (IsLocalization.Away.algebraMap_isUnit b)

/-- Points of `Spec A[1/b]` map into `D(n)` in `Spec A[1/a]` when `a ∣ b` and `n ∣ b`. -/
lemma algebraMap_notMem_comap {a b n : A} (hab : a ∣ b) (hn : n ∣ b)
    (y : PrimeSpectrum (Localization.Away b)) :
    algebraMap A (Localization.Away a) n ∉
      (PrimeSpectrum.comap (awayMap hab) y).asIdeal := by
  intro hmem
  change awayMap hab (algebraMap A _ n) ∈ y.asIdeal at hmem
  rw [awayMap_algebraMap] at hmem
  exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (unit_of_dvd hn))

end Restrict

section Setup

variable {s : Spec R} {Y : Over (Spec ((Spec R).presheaf.stalk s))}
  (e : (baseChange ((Spec R).fromSpecStalk s) F).RepresentableBy Y)
variable {B : Type u} [CommRing B] [Algebra R B]
  (t : Spec (CommRingCat.of B) ⟶ Spec ((Spec R).presheaf.stalk s))
  (ht : t ≫ (Spec R).fromSpecStalk s = (ovR R B).hom)
  (j : Over.mk t ⟶ Y) [IsOpenImmersion j.left]
variable {A : Type u} [CommRing A] [Algebra R A] [Algebra A B] [IsScalarTower R A B]
  (M : Submonoid A) [IsLocalization M B]
  (ξ : F.obj (op (ovR R A)))

omit [IsOpenImmersion j.left] in
lemma map_toLocₐ_resA
    (hξ : F.map (homR (IsScalarTower.toAlgHom R A B)).op ξ =
      elemEquiv ((Spec R).fromSpecStalk s) e (ovR R B) t ht j)
    (a : A) (ha : a ∈ M) :
    F.map (homR (toLocₐ M B (DivIndex.mk a ha))).op (resA ξ a) =
      elemEquiv ((Spec R).fromSpecStalk s) e (ovR R B) t ht j := by
  have : (toLocₐ M B (DivIndex.mk a ha)).comp
      (IsScalarTower.toAlgHom R A (Localization.Away a)) = IsScalarTower.toAlgHom R A B :=
    AlgHom.ext (toLoc_algebraMap M B (DivIndex.mk a ha))
  rw [resA, map_homR_map_homR, this, hξ]

/-- (D) The restriction of `ξ` to `Spec A[1/a]`, `a ∈ M`, is infinitesimally étale at every
point whose prime is disjoint from `M`. -/
theorem infinitesimallyEtaleAt_resA
    (hξ : F.map (homR (IsScalarTower.toAlgHom R A B)).op ξ =
      elemEquiv ((Spec R).fromSpecStalk s) e (ovR R B) t ht j)
    (a : A) (ha : a ∈ M) (y : (ovR R (Localization.Away a)).left)
    (hy : ∀ m ∈ M, algebraMap A (Localization.Away a) m ∉ y.asIdeal) :
    InfinitesimallyEtaleAt F (resA ξ a) y := by
  let a' : DivIndex M := DivIndex.mk a ha
  let ρ : ovR R B ⟶ ovR R (Localization.Away a) := homR (toLocₐ M B a')
  have hloc : (toLoc M B a').comp (algebraMap A (Localization.Away a)) = algebraMap A B :=
    RingHom.ext (toLoc_algebraMap M B a')
  apply infinitesimallyEtaleAt_of_factor ρ
  · intro L _ _ _ w hw
    let ψ : CommRingCat.of (Localization.Away a) ⟶ CommRingCat.of L := Spec.preimage w
    have hψ : Spec.map ψ = w := Spec.map_preimage w
    have hunit : ∀ m : M, IsUnit ((ψ.hom.comp (algebraMap A (Localization.Away a))) m) := by
      intro m
      have h1 := hw (IsLocalRing.closedPoint L)
      rw [← hψ] at h1
      change PrimeSpectrum.comap ψ.hom (IsLocalRing.closedPoint L) = y at h1
      have hm := hy m m.2
      rw [← h1] at hm
      by_contra hcon
      exact hm ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hcon))
    let χ : B →+* L := IsLocalization.lift hunit
    have hχ : χ.comp (algebraMap A B) = ψ.hom.comp (algebraMap A (Localization.Away a)) :=
      IsLocalization.lift_comp hunit
    have hχ' : χ.comp (toLoc M B a') = ψ.hom := by
      apply IsLocalization.ringHom_ext (Submonoid.powers a)
      rw [RingHom.comp_assoc, hloc, hχ]
    refine ⟨Spec.map (CommRingCat.ofHom χ), ?_, ?_⟩
    · change Spec.map (CommRingCat.ofHom χ) ≫
        Spec.map (CommRingCat.ofHom (toLoc M B a')) = w
      rw [← hψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hχ']
      rfl
    · intro w' hw'
      let χ'' : CommRingCat.of B ⟶ CommRingCat.of L := Spec.preimage w'
      have hχ'' : Spec.map χ'' = w' := Spec.map_preimage w'
      have h2 : Spec.map (CommRingCat.ofHom (toLoc M B a') ≫ χ'') = Spec.map ψ := by
        rw [Spec.map_comp, hχ'', hψ]
        exact hw'
      have h3 : χ''.hom.comp (toLoc M B a') = ψ.hom :=
        congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
      have h4 : χ''.hom = χ := by
        apply IsLocalization.ringHom_ext M
        rw [hχ, ← hloc, ← RingHom.comp_assoc, h3]
      rw [← hχ'']
      congr 1
      exact CommRingCat.hom_ext h4
  · intro y' _
    have hg := fromSpecStalk_factor (X := Spec R) s
    have key := infinitesimallyEtaleAt_elemEquiv ((Spec R).fromSpecStalk s) e hg t ht j y'
    rw [← map_toLocₐ_resA e t ht j M ξ hξ a ha] at key
    exact key

/-- Étale shrinking: if the étale locus of `ξ` restricted to `Spec A[1/a]` is open, then the
restriction to `Spec A[1/b]` is infinitesimally étale everywhere for all `b` divisible by
`a * n`, for some `n ∈ M`. -/
theorem exists_etale
    (hξ : F.map (homR (IsScalarTower.toAlgHom R A B)).op ξ =
      elemEquiv ((Spec R).fromSpecStalk s) e (ovR R B) t ht j)
    (a : A) (ha : a ∈ M)
    (hopen : IsOpen {y : PrimeSpectrum (Localization.Away a) |
      InfinitesimallyEtaleAt F (resA ξ a) y}) :
    ∃ n ∈ M, ∀ b : A, a * n ∣ b → ∀ y, InfinitesimallyEtaleAt F (resA ξ b) y := by
  obtain ⟨m', hm', hsub⟩ := exists_mem_basicOpen_subset
    (M.map (algebraMap A (Localization.Away a))) hopen (fun q hq =>
      infinitesimallyEtaleAt_resA e t ht j M ξ hξ a ha q (fun m hm hmq =>
        Set.disjoint_left.1 hq (Submonoid.mem_map_of_mem _ hm) hmq))
  obtain ⟨n, hn, rfl⟩ := hm'
  refine ⟨n, hn, fun b hb y => ?_⟩
  have hab : a ∣ b := dvd_trans (dvd_mul_right a n) hb
  have hnb : n ∣ b := dvd_trans (dvd_mul_left n a) hb
  rw [← resA_awayMapₐ ξ hab]
  apply infinitesimallyEtaleAt_restrict (homR (awayMapₐ (R := R) hab))
  apply hsub
  exact algebraMap_notMem_comap hab hnb y

end Setup

section Unramified

variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Algebra A B]
  [IsScalarTower R A B] (M : Submonoid A) [IsLocalization M B]

/-- Unramified shrinking. -/
theorem exists_unramified [Algebra.FiniteType R A] [Algebra.FormallyUnramified R B] :
    ∃ m₁ ∈ M, ∀ a : A, m₁ ∣ a → Algebra.FormallyUnramified R (Localization.Away a) := by
  obtain ⟨m₁, hm₁, hsub⟩ := exists_mem_basicOpen_subset M Algebra.isOpen_unramifiedLocus
    (fun q hq => mem_unramifiedLocus (R := R) (B := B) M q hq)
  refine ⟨m₁, hm₁, fun a ha => Algebra.basicOpen_subset_unramifiedLocus_iff.1 ?_⟩
  intro x hx
  apply hsub
  intro hm
  obtain ⟨c, rfl⟩ := ha
  exact hx (x.asIdeal.mul_mem_right c hm)

end Unramified

end Charts

end Langlands.AlgebraicGeometry.UnramifiedFunctor
