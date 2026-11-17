import Langlands.GroupScheme.NormalQuotientFppfOpenGluing
import Langlands.GroupScheme.NormalQuotientEtaleGluing

/-! # Affine normal quotients supplied on an fppf cover -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.NormalQuotient

/-- A finite affine fppf cover of an affine base suffices for effective descent
of supplied affine quotients. -/
theorem exists_affine_fppfQuotient_of_finiteAffineFppfCover
    {S : Scheme.{u}} [IsAffine S]
    {G N : GroupScheme S} [IsAffineHom G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormal)
    (𝒱 : Scheme.AffineCover.{u} (@Flat ⊓ @LocallyOfFinitePresentation) S) [Finite 𝒱.I₀]
    (Q : ∀ j, GroupScheme (𝒱.cover.X j))
    (q : ∀ j, (baseChange (𝒱.cover.f j)).obj G ⟶ Q j)
    (hQ : ∀ j, IsAffineHom (Q j).X.hom)
    (hq : ∀ j, RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange (𝒱.cover.f j)).map i)) (q j)) :
    ∃ (M : GroupScheme S) (r : G ⟶ M), IsAffineHom M.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r := by
  let C : Scheme.{u} := ∐ 𝒱.cover.X
  let p : C ⟶ S := Sigma.desc 𝒱.cover.f
  have : Finite 𝒱.cover.I₀ := ‹Finite 𝒱.I₀›
  have : ∀ j, IsAffine (𝒱.cover.X j) := fun _ => inferInstance
  have : IsAffine C := inferInstanceAs (IsAffine (∐ 𝒱.cover.X))
  have : Flat p := IsZariskiLocalAtSource.sigmaDesc fun j => (𝒱.cover.map_prop j).1
  have : Surjective p := by
    constructor
    intro s
    obtain ⟨j, x, rfl⟩ := 𝒱.cover.exists_eq s
    refine ⟨Sigma.ι 𝒱.cover.X j x, ?_⟩
    change (Sigma.desc 𝒱.cover.f) ((Sigma.ι 𝒱.cover.X j) x) = _
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  let G' := (baseChange p).obj G
  let N' := (baseChange p).obj N
  let i' : N' ⟶ G' := (baseChange p).map i
  have : IsAffineHom G'.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom p))
  have : Mono i'.hom.hom := by
    change Mono ((Over.pullback p).map i.hom.hom)
    infer_instance
  have hn' : (SubgroupFunctor.range i').IsNormal := by
    dsimp [i']
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hn.baseChange p
  let 𝒲 := sigmaOpenCover 𝒱.cover.X
  have hlocal : ∀ j, ∃ qj : (baseChange (𝒲.f j)).obj G' ⟶ Q j,
      RelativeRoot.IsFppfQuotient
        (SubgroupFunctor.range ((baseChange (𝒲.f j)).map i')) qj := by
    intro j
    have hj : 𝒲.f j ≫ p = 𝒱.cover.f j := by
      dsimp [𝒲, sigmaOpenCover, p]
      simp
    obtain ⟨qj, hqj⟩ : ∃ qj : (baseChange (𝒲.f j ≫ p)).obj G ⟶ Q j,
        RelativeRoot.IsFppfQuotient
          (SubgroupFunctor.range ((baseChange (𝒲.f j ≫ p)).map i)) qj := by
      rw [hj]
      exact ⟨q j, hq j⟩
    exact ⟨_, hqj.comp_baseChange p (𝒲.f j) i qj⟩
  choose q' hq' using hlocal
  obtain ⟨Q', q', hQ', hq'⟩ :=
    exists_affine_fppfQuotient_of_openCover_arbitrary_kernel i' hn' 𝒲 Q q' hQ hq'
  let := hQ'
  have : IsAffine Q'.X.left := isAffine_of_isAffineHom Q'.X.hom
  have : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
  have : QuasiCompact q'.hom.hom.left := inferInstance
  obtain ⟨M, r, hM, hr, _⟩ := Descent.exists_affine_fppfQuotient p i Q' q' hq'
  let := hM
  exact ⟨M, r, inferInstance, hr⟩

/-- Supplied affine quotients on an arbitrary fppf cover descend over an
affine base, after choosing a finite affine refinement. -/
theorem exists_affine_fppfQuotient_of_fppfCover_affineBase
    {S : Scheme.{u}} [IsAffine S]
    {G N : GroupScheme S} [IsAffineHom G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormal)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S)
    (Q : ∀ j, GroupScheme (𝒰.X j))
    (q : ∀ j, (baseChange (𝒰.f j)).obj G ⟶ Q j)
    (hQ : ∀ j, IsAffineHom (Q j).X.hom)
    (hq : ∀ j, RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) (q j)) :
    ∃ (M : GroupScheme S) (r : G ⟶ M), IsAffineHom M.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r := by
  have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap fun j => by
      have : Flat (𝒰.f j) := (𝒰.map_prop j).1
      have : LocallyOfFinitePresentation (𝒰.f j) := (𝒰.map_prop j).2
      exact (𝒰.f j).isOpenMap
  obtain ⟨𝒱, f, hf, _⟩ := QuasiCompactCover.exists_hom.{u, u} 𝒰
  let := hf
  have hlocal : ∀ j, ∃ (Qj : GroupScheme (𝒱.cover.X j))
      (qj : (baseChange (𝒱.cover.f j)).obj G ⟶ Qj),
      IsAffineHom Qj.X.hom ∧ RelativeRoot.IsFppfQuotient
        (SubgroupFunctor.range ((baseChange (𝒱.cover.f j)).map i)) qj := by
    intro j
    let Qj := (baseChange (f.h₀ j)).obj (Q (f.s₀ j))
    let := hQ (f.s₀ j)
    have hQj : IsAffineHom Qj.X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd (Q (f.s₀ j)).X.hom (f.h₀ j)))
    have hex : ∃ qj : (baseChange (f.h₀ j ≫ 𝒰.f (f.s₀ j))).obj G ⟶ Qj,
        RelativeRoot.IsFppfQuotient
          (SubgroupFunctor.range ((baseChange (f.h₀ j ≫ 𝒰.f (f.s₀ j))).map i)) qj :=
      ⟨_, (hq (f.s₀ j)).baseChange_comp (𝒰.f (f.s₀ j)) (f.h₀ j) i (q (f.s₀ j))⟩
    rw [f.w₀ j] at hex
    obtain ⟨qj, hqj⟩ := hex
    exact ⟨Qj, qj, hQj, hqj⟩
  choose Q' q' hQ' hq' using hlocal
  exact exists_affine_fppfQuotient_of_finiteAffineFppfCover i hn 𝒱 Q' q' hQ' hq'

/-- Supplied affine normal quotients on an fppf base cover glue over an
arbitrary base scheme. -/
theorem exists_affine_fppfQuotient_of_fppfCover
    {S : Scheme.{u}}
    {G N : GroupScheme S} [IsAffineHom G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormal)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S)
    (Q : ∀ j, GroupScheme (𝒰.X j))
    (q : ∀ j, (baseChange (𝒰.f j)).obj G ⟶ Q j)
    (hQ : ∀ j, IsAffineHom (Q j).X.hom)
    (hq : ∀ j, RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) (q j)) :
    ∃ (M : GroupScheme S) (r : G ⟶ M), IsAffineHom M.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r := by
  have hlocal : ∀ j, ∃ (M : GroupScheme (S.affineCover.X j))
      (r : (baseChange (S.affineCover.f j)).obj G ⟶ M),
      IsAffineHom M.X.hom ∧ RelativeRoot.IsFppfQuotient
        (SubgroupFunctor.range ((baseChange (S.affineCover.f j)).map i)) r := by
    intro j
    let b := S.affineCover.f j
    let G' := (baseChange b).obj G
    let N' := (baseChange b).obj N
    let i' : N' ⟶ G' := (baseChange b).map i
    have : IsAffineHom G'.X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
    have : Mono i'.hom.hom := by
      change Mono ((Over.pullback b).map i.hom.hom)
      infer_instance
    have hn' : (SubgroupFunctor.range i').IsNormal := by
      dsimp [i']
      rw [SubgroupFunctor.range_baseChangeHom]
      exact hn.baseChange b
    let 𝒱 := 𝒰.pullback₁ b
    have hquot : ∀ k, ∃ (Qk : GroupScheme (𝒱.X k))
        (qk : (baseChange (𝒱.f k)).obj G' ⟶ Qk),
        IsAffineHom Qk.X.hom ∧ RelativeRoot.IsFppfQuotient
          (SubgroupFunctor.range ((baseChange (𝒱.f k)).map i')) qk := by
      intro k
      let c := 𝒰.pullbackHom b k
      let Qk := (baseChange c).obj (Q k)
      have hQk : IsAffineHom Qk.X.hom :=
        MorphismProperty.pullback_snd (Q k).X.hom c (hQ k)
      have hex : ∃ qk : (baseChange (c ≫ 𝒰.f k)).obj G ⟶ Qk,
          RelativeRoot.IsFppfQuotient
            (SubgroupFunctor.range ((baseChange (c ≫ 𝒰.f k)).map i)) qk :=
        ⟨_, (hq k).baseChange_comp (𝒰.f k) c i (q k)⟩
      have hc : c ≫ 𝒰.f k = 𝒱.f k ≫ b := 𝒰.pullbackHom_map b k
      rw [hc] at hex
      obtain ⟨qk, hqk⟩ := hex
      exact ⟨Qk, _, hQk, hqk.comp_baseChange b (𝒱.f k) i qk⟩
    choose Q' q' hQ' hq' using hquot
    exact exists_affine_fppfQuotient_of_fppfCover_affineBase i' hn' 𝒱 Q' q' hQ' hq'
  choose M r hM hr using hlocal
  exact exists_affine_fppfQuotient_of_openCover_arbitrary_kernel i hn S.affineCover M r hM hr

/-- A chosen affine quotient descended from supplied local fppf quotients. -/
def affineFppfQuotientOfCover
    {S : Scheme.{u}} {G N : GroupScheme S} [IsAffineHom G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom]
    (hn : (SubgroupFunctor.range i).IsNormal)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S)
    (Q : ∀ j, GroupScheme (𝒰.X j))
    (q : ∀ j, (baseChange (𝒰.f j)).obj G ⟶ Q j)
    (hQ : ∀ j, IsAffineHom (Q j).X.hom)
    (hq : ∀ j, RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) (q j)) :
    Σ (M : GroupScheme S), {r : G ⟶ M // IsAffineHom M.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r} := by
  let h := exists_affine_fppfQuotient_of_fppfCover i hn 𝒰 Q q hQ hq
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose_spec (Classical.choose_spec h)⟩

end Langlands.GroupScheme.NormalQuotient
