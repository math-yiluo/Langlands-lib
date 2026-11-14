import Langlands.GroupScheme.NormalQuotientOpenGluing
import Langlands.GroupScheme.Descent.AffineFppfQuotient
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.Cover.Sigma
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Étale descent of affine normal quotient schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace RelativeRoot.IsFppfQuotient

/-- Changing the source and represented kernel by a compatible pair of
isomorphisms preserves the actual fppf quotient. -/
theorem of_iso_square {S : Scheme.{u}} {G G' N N' Q : GroupScheme S}
    (i : N ⟶ G) (i' : N' ⟶ G') (q : G ⟶ Q)
    (eG : G' ≅ G) (eN : N' ≅ N)
    (hcomm : i' ≫ eG.hom = eN.hom ≫ i)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i') (eG.hom ≫ q) := by
  have := hq.1
  have := hq.2.1
  have := hq.2.2.1
  have : IsIso eG.hom.hom.hom.left := (Over.forget S).map_isIso eG.hom.hom.hom
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Flat (eG.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · change Surjective (eG.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · change LocallyOfFinitePresentation (eG.hom.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  · have hc := congrArg (fun f => f.hom.hom) hcomm
    simp only [Grp.comp_hom_hom] at hc
    ext T x
    rw [mem_range_kernelι_iff, Grp.comp_hom_hom, ← Category.assoc,
      ← mem_range_kernelι_iff, hq.2.2.2, SubgroupFunctor.mem_range,
      SubgroupFunctor.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨y ≫ eN.inv.hom.hom, ?_⟩
      apply (cancel_mono eG.hom.hom.hom).mp
      rw [Category.assoc, Category.assoc, hc]
      simpa only [← Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
        Grp.id_hom_hom, Category.comp_id, Category.id_comp] using hy
    · rintro ⟨y, rfl⟩
      refine ⟨y ≫ eN.hom.hom.hom, ?_⟩
      simpa only [Category.assoc] using (congrArg (fun z => y ≫ z) hc.symm)

/-- Coherence of pullback composition transports the original quotient map. -/
theorem baseChange_comp {S S' S'' : Scheme.{u}} (b : S' ⟶ S) (c : S'' ⟶ S')
    {G N : GroupScheme S} (i : N ⟶ G) {Q : GroupScheme S'}
    (q : (GroupScheme.baseChange b).obj G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange b).map i)) q) :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((GroupScheme.baseChange (c ≫ b)).map i))
      ((baseChangeCompIso b c G).hom ≫ (GroupScheme.baseChange c).map q) := by
  apply of_iso_square ((GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map i))
    ((GroupScheme.baseChange (c ≫ b)).map i) ((GroupScheme.baseChange c).map q)
    (baseChangeCompIso b c G) (baseChangeCompIso b c N)
  · exact ((Functor.mapGrpNatIso (Over.pullbackComp c b)) ≪≫
      Functor.mapGrpCompIso).hom.naturality i
  · simpa only [SubgroupFunctor.range_baseChangeHom] using hq.baseChange c

/-- The inverse composition comparison also preserves the supplied quotient. -/
theorem comp_baseChange {S S' S'' : Scheme.{u}} (b : S' ⟶ S) (c : S'' ⟶ S')
    {G N : GroupScheme S} (i : N ⟶ G) {Q : GroupScheme S''}
    (q : (GroupScheme.baseChange (c ≫ b)).obj G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange (c ≫ b)).map i)) q) :
    RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map i)))
      ((baseChangeCompIso b c G).inv ≫ q) := by
  apply of_iso_square ((GroupScheme.baseChange (c ≫ b)).map i)
    ((GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map i)) q
    (baseChangeCompIso b c G).symm (baseChangeCompIso b c N).symm
  · exact ((Functor.mapGrpNatIso (Over.pullbackComp c b)) ≪≫
      Functor.mapGrpCompIso).inv.naturality i
  · exact hq

end RelativeRoot.IsFppfQuotient

namespace NormalQuotient

/-- A finite affine étale cover of an affine base suffices for effective descent
of supplied affine quotients. -/
theorem exists_affine_fppfQuotient_of_finiteAffineEtaleCover
    {S : Scheme.{u}} [IsAffine S]
    {G N : GroupScheme S} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom] (hN : Smooth N.X.hom)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (𝒱 : Scheme.AffineCover.{u} @Etale S) [Finite 𝒱.I₀]
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
  have : Etale p := IsZariskiLocalAtSource.sigmaDesc 𝒱.cover.map_prop
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
  have : LocallyOfFiniteType G'.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom p))
  have : Mono i'.hom.hom := by
    change Mono ((Over.pullback p).map i.hom.hom)
    infer_instance
  have hN' : Smooth N'.X.hom := by
    let := hN
    exact inferInstanceAs (Smooth (pullback.snd N.X.hom p))
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
    exists_affine_fppfQuotient_of_openCover i' hN' hn' 𝒲 Q q' hQ hq'
  let := hQ'
  have : IsAffine Q'.X.left := isAffine_of_isAffineHom Q'.X.hom
  have : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
  have : QuasiCompact q'.hom.hom.left := inferInstance
  obtain ⟨M, r, hM, hr, _⟩ := Descent.exists_affine_fppfQuotient p i Q' q' hq'
  let := hM
  exact ⟨M, r, inferInstance, hr⟩

/-- Supplied affine quotients on an arbitrary étale cover descend over an
affine base, after choosing a finite affine refinement. -/
theorem exists_affine_fppfQuotient_of_etaleCover_affineBase
    {S : Scheme.{u}} [IsAffine S]
    {G N : GroupScheme S} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom] (hN : Smooth N.X.hom)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (Q : ∀ j, GroupScheme (𝒰.X j))
    (q : ∀ j, (baseChange (𝒰.f j)).obj G ⟶ Q j)
    (hQ : ∀ j, IsAffineHom (Q j).X.hom)
    (hq : ∀ j, RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) (q j)) :
    ∃ (M : GroupScheme S) (r : G ⟶ M), IsAffineHom M.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r := by
  have : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap fun j => (𝒰.f j).isOpenMap
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
  exact exists_affine_fppfQuotient_of_finiteAffineEtaleCover i hN hn 𝒱 Q' q' hQ' hq'

/-- Supplied affine normal quotients on an étale base cover glue over an
arbitrary base scheme. -/
theorem exists_affine_fppfQuotient_of_etaleCover
    {S : Scheme.{u}}
    {G N : GroupScheme S} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom] (hN : Smooth N.X.hom)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
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
    have : LocallyOfFiniteType G'.X.hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom b))
    have : Mono i'.hom.hom := by
      change Mono ((Over.pullback b).map i.hom.hom)
      infer_instance
    have hN' : Smooth N'.X.hom := by
      let := hN
      exact inferInstanceAs (Smooth (pullback.snd N.X.hom b))
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
    exact exists_affine_fppfQuotient_of_etaleCover_affineBase i' hN' hn' 𝒱 Q' q' hQ' hq'
  choose M r hM hr using hlocal
  exact exists_affine_fppfQuotient_of_openCover i hN hn S.affineCover M r hM hr

/-- Pointwise étale neighbourhoods carrying affine quotients suffice; a single
global quasi-compact cover is not an extra hypothesis. -/
theorem exists_affine_fppfQuotient_of_pointwise_etale
    {S : Scheme.{u}}
    {G N : GroupScheme S} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom] (hN : Smooth N.X.hom)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (hlocal : ∀ s : S, ∃ (T : Scheme.{u}) (b : T ⟶ S)
      (Q : GroupScheme T) (q : (baseChange b).obj G ⟶ Q),
      Etale b ∧ s ∈ Set.range b ∧ IsAffineHom Q.X.hom ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((baseChange b).map i)) q) :
    ∃ (M : GroupScheme S) (r : G ⟶ M), IsAffineHom M.X.hom ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r := by
  choose T b Q q hb hs hQ hq using hlocal
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    { I₀ := S
      X := T
      f := b
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun s => ⟨s, hs s⟩, hb⟩ }
  exact exists_affine_fppfQuotient_of_etaleCover i hN hn 𝒰 Q q hQ hq

end NormalQuotient

/-- Étale-cover gluing of supplied affine quotients by a smooth normal subgroup. -/
def AffineNormalQuotientEtaleGluingStatement : Prop :=
  ∀ (S : Scheme.{u}) (G N : GroupScheme S)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : N ⟶ G) [Mono i.hom.hom],
    Smooth N.X.hom → (SubgroupFunctor.range i).IsNormal →
    ∀ (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
      (Q : ∀ j, GroupScheme (𝒰.X j))
      (q : ∀ j, (baseChange (𝒰.f j)).obj G ⟶ Q j),
      (∀ j, IsAffineHom (Q j).X.hom) →
      (∀ j, RelativeRoot.IsFppfQuotient
        (SubgroupFunctor.range ((baseChange (𝒰.f j)).map i)) (q j)) →
      ∃ (M : GroupScheme S) (r : G ⟶ M), IsAffineHom M.X.hom ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) r

/-- Supplied étale-local affine quotients glue in every universe. -/
theorem affineNormalQuotientEtaleGluing : AffineNormalQuotientEtaleGluingStatement.{u} := by
  intro S G N _ _ i _ hN hn 𝒰 Q q hQ hq
  exact NormalQuotient.exists_affine_fppfQuotient_of_etaleCover i hN hn 𝒰 Q q hQ hq

end Langlands.GroupScheme
