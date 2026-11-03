import Langlands.GroupScheme.Rational.BruhatCoveringReduction
import Langlands.GroupScheme.Rational.TorusNormalizer
import Langlands.GroupScheme.Rational.MinimalParabolicStatement
import Langlands.GroupScheme.Rational.ParabolicTorusStatement
import Langlands.GroupScheme.Rational.MinimalParabolicContainment
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Dynamic.Uniqueness
import Langlands.GroupScheme.Dynamic.Decomposition
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # Surjectivity of `N(k)/Z(k) → N(U)/Z(U)` from rational structure statements

For a maximal split torus `i : T ⟶ G` of a connected reductive group over a field `k`, a test
scheme `U` and a point `g` of the torus normalizer over `U` that acts on `T` through one
automorphism `σ` of `T`, this module produces a rational normalizing point `n` with
`n|_U⁻¹ * g` in the torus centralizer over `U`. The argument is that of Borel–Tits 5.3: choose
a cocharacter `ν` such that `ν` and `ν ≫ σ` are both generic, conjugate the two minimal
parabolics `P(ν)` and `P(ν ≫ σ)` by a rational normalizing point, and use that a parabolic is
its own normalizer and that `P(ν)` meets the torus normalizer in the torus centralizer.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeWeylSurjective

/-! ### Transport of dynamic parabolics by a conjugating point -/

section Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- A point `h` over `U` conjugates the cocharacter `χ` into `χ'` when, after every refinement
`a : V ⟶ U`, conjugation by `a ≫ h` sends `χ(s)` to `χ'(s)` for every point `s` of `𝔾_m`. -/
def ConjugatesCocharacter {U : Over S} (h : U ⟶ G.X) (χ χ' : (Gm S).toGrp ⟶ G) : Prop :=
  ∀ (V : Over S) (a : V ⟶ U) (s : V ⟶ (Gm S).X),
    (a ≫ h) * (s ≫ χ.hom.hom) * (a ≫ h)⁻¹ = s ≫ χ'.hom.hom

theorem ConjugatesCocharacter.inv {U : Over S} {h : U ⟶ G.X} {χ χ' : (Gm S).toGrp ⟶ G}
    (hh : ConjugatesCocharacter h χ χ') : ConjugatesCocharacter h⁻¹ χ' χ := by
  intro V a s
  rw [GrpObj.comp_inv, inv_inv, ← hh V a s]
  group

/-- A point conjugating `χ` into `χ'` conjugates `P(χ)` into `P(χ')`: the conjugate of an orbit
extension is an orbit extension. -/
theorem ConjugatesCocharacter.conj_mem_parabolic {U : Over S} {h : U ⟶ G.X}
    {χ χ' : (Gm S).toGrp ⟶ G} (hh : ConjugatesCocharacter h χ χ') {V : Over S} (a : V ⟶ U)
    {x : V ⟶ G.X} (hx : x ∈ (Dynamic.parabolic χ).carrier V) :
    (a ≫ h) * x * (a ≫ h)⁻¹ ∈ (Dynamic.parabolic χ').carrier V := by
  obtain ⟨e, he⟩ := hx
  refine ⟨(fst V (AffineLine.scheme S) ≫ a ≫ h) * e *
    (fst V (AffineLine.scheme S) ≫ a ≫ h)⁻¹, ?_⟩
  have hs := hh (V ⊗ (Gm S).X) (fst V (Gm S).X ≫ a) (snd V (Gm S).X)
  rw [Dynamic.IsOrbitExtension, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, he,
    whiskerLeft_fst_assoc]
  simp only [Dynamic.orbit, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc] at hs ⊢
  rw [← hs]
  group

/-- If a rational point `n` conjugates `P(χ)` onto `P(χ')` and `g` conjugates `χ` into `χ'`,
then `n⁻¹ g` normalizes `P(χ)`. -/
theorem constantPoint_inv_mul_mem_normalizer {U : Over S} (n : Over.mk (𝟙 S) ⟶ G.X)
    {g : U ⟶ G.X} {χ χ' : (Gm S).toGrp ⟶ G}
    (hn : Dynamic.parabolic χ = (Dynamic.parabolic χ').comap (G.innerIso n).hom)
    (hg : ConjugatesCocharacter g χ χ') :
    (G.constantPoint n U)⁻¹ * g ∈ (Dynamic.parabolic χ).normalizer.carrier U := by
  have hmem : ∀ (V : Over S) (x : V ⟶ G.X), x ∈ (Dynamic.parabolic χ).carrier V ↔
      G.constantPoint n V * x * (G.constantPoint n V)⁻¹ ∈
        (Dynamic.parabolic χ').carrier V := by
    intro V x
    conv_lhs => rw [hn]
    rw [SubgroupFunctor.mem_comap, comp_innerIso_hom]
  intro V a x hx
  have hc : a ≫ ((G.constantPoint n U)⁻¹ * g) = (G.constantPoint n V)⁻¹ * (a ≫ g) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, G.constantPoint_naturality]
  rw [hc]
  constructor
  · rw [hmem]
    convert hg.conj_mem_parabolic a hx using 1
    group
  · have h2 := hg.inv.conj_mem_parabolic a ((hmem V x).mp hx)
    rw [GrpObj.comp_inv] at h2
    convert h2 using 1
    group

/-- A point of `P(χ)` normalizing `i` centralizes `i`, provided `i` lies in `Z(χ)` and `Z(χ)`
centralizes `i`. The limit `l` of the point lies in `Z(χ)`, and the commutator of `m l⁻¹` with a
torus point lies both in `U(χ)` and in the torus, hence in `U(χ) ∩ Z(χ) = 1`. -/
theorem mem_torusCentralizer_of_mem_parabolic [IsSeparated G.X.hom] {T : CommGroupScheme S}
    (i : T.toGrp ⟶ G) (χ : (Gm S).toGrp ⟶ G)
    (hrange : SubgroupFunctor.range i ≤ Dynamic.centralizer χ)
    (hcent : Dynamic.centralizer χ ≤ torusCentralizer i) {U : Over S} {m : U ⟶ G.X}
    (hmN : m ∈ (torusNormalizer i).carrier U) (hmP : m ∈ (Dynamic.parabolic χ).carrier U) :
    m ∈ (torusCentralizer i).carrier U := by
  have huniq : ∀ (W : Over S) (g l l' : W ⟶ G.X), Dynamic.HasLimit χ g l →
      Dynamic.HasLimit χ g l' → l = l' := fun _ _ _ _ hl hl' => hl.unique χ hl'
  obtain ⟨l, hl⟩ := Dynamic.exists_hasLimit χ hmP
  have hlZ : l ∈ (Dynamic.centralizer χ).carrier U := hl.mem_centralizer χ
  have hlC : l ∈ (torusCentralizer i).carrier U := hcent U hlZ
  have hu : m * l⁻¹ ∈ (Dynamic.unipotent χ).carrier U := by
    have h := hl.mul χ (Dynamic.hasLimit_of_mem_centralizer χ hlZ).inv
    rwa [mul_inv_cancel] at h
  have huN : m * l⁻¹ ∈ (torusNormalizer i).carrier U :=
    ((torusNormalizer i).carrier U).mul_mem hmN
      (((torusNormalizer i).carrier U).inv_mem (torusCentralizer_le_torusNormalizer i U hlC))
  have huC : m * l⁻¹ ∈ (torusCentralizer i).carrier U := by
    refine (mem_torusCentralizer i).mpr fun W b t => ?_
    have hvU : b ≫ (m * l⁻¹) ∈ (Dynamic.unipotent χ).carrier W :=
      (Dynamic.unipotent χ).comp_mem b hu
    obtain ⟨⟨t', ht'⟩, -⟩ := (mem_torusNormalizer i).mp huN W b t
    have htZ : t ≫ i.hom.hom ∈ (Dynamic.centralizer χ).carrier W :=
      hrange W (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩)
    have ht'Z : t' ≫ i.hom.hom ∈ (Dynamic.centralizer χ).carrier W :=
      hrange W (SubgroupFunctor.mem_range.mpr ⟨t', rfl⟩)
    have htP : t ≫ i.hom.hom ∈ (Dynamic.parabolic χ).carrier W :=
      Dynamic.centralizer_le_parabolic χ W htZ
    have hc1 : (b ≫ (m * l⁻¹)) * (t ≫ i.hom.hom) * (b ≫ (m * l⁻¹))⁻¹ * (t ≫ i.hom.hom)⁻¹ ∈
        (Dynamic.unipotent χ).carrier W := by
      have h := Dynamic.conj_mem_unipotent χ htP (((Dynamic.unipotent χ).carrier W).inv_mem hvU)
      have h2 := ((Dynamic.unipotent χ).carrier W).mul_mem hvU h
      convert h2 using 1
      group
    have hc2 : (b ≫ (m * l⁻¹)) * (t ≫ i.hom.hom) * (b ≫ (m * l⁻¹))⁻¹ * (t ≫ i.hom.hom)⁻¹ ∈
        (Dynamic.centralizer χ).carrier W := by
      rw [ht']
      exact ((Dynamic.centralizer χ).carrier W).mul_mem ht'Z
        (((Dynamic.centralizer χ).carrier W).inv_mem htZ)
    have h1 := Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent χ huniq hc2 hc1
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)
  have h := ((torusCentralizer i).carrier U).mul_mem huC hlC
  rwa [inv_mul_cancel_right] at h

end Dynamic

/-! ### Rational conjugation of minimal parabolics -/

section Conjugation

variable {S : Scheme.{u}}

/-- If `j ≫ φ = E ≫ j'` for isomorphisms `φ` of `G` and `E : P ≅ P'`, then the points of `j` are
the preimage under `φ` of the points of `j'`. -/
theorem range_eq_comap_of_comp_eq {P P' G : GroupScheme S} {j : P ⟶ G} {j' : P' ⟶ G}
    (φ : G ≅ G) (E : P ≅ P') (h : j ≫ φ.hom = E.hom ≫ j') :
    SubgroupFunctor.range j = (SubgroupFunctor.range j').comap φ.hom := by
  have h' : j' ≫ φ.inv = E.inv ≫ j := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  apply SubgroupFunctor.ext
  intro V
  ext x
  rw [SubgroupFunctor.mem_comap, SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ E.hom.hom.hom, ?_⟩
    rw [Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, h]
  · rintro ⟨z, hz⟩
    refine ⟨z ≫ E.inv.hom.hom, ?_⟩
    have hx : x = (x ≫ φ.hom.hom.hom) ≫ φ.inv.hom.hom := by
      rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id]
      rfl
    rw [hx, ← hz, Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, h']

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Two minimal parabolics `P(χ)` and `P(χ')` attached to cocharacters of a maximal split torus
`i` are conjugate by a rational point normalizing `i`. First conjugate the parabolics by any
rational point `h`, then conjugate the two maximal split tori `i ≫ Int(h)` and `i` of the second
parabolic by a rational point `p` of it; then `n = p h` works. -/
theorem exists_normalizingPoint_comap_eq
    (hconj : MinimalParabolicConjugacyStatement.{u})
    (htorus : MinimalParabolicSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (χ χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp)
    {P P' : GroupScheme (Spec (CommRingCat.of k))} {j : P ⟶ G} {j' : P' ⟶ G}
    (hj : IsMinimalParabolicSubgroup j) (hj' : IsMinimalParabolicSubgroup j')
    (hPj : SubgroupFunctor.range j = Dynamic.parabolic (χ ≫ i))
    (hPj' : SubgroupFunctor.range j' = Dynamic.parabolic (χ' ≫ i)) :
    ∃ n ∈ normalizerPoints i,
      Dynamic.parabolic (χ ≫ i) = (Dynamic.parabolic (χ' ≫ i)).comap (G.innerIso n).hom := by
  obtain ⟨h, e, hje⟩ := hconj k G hG P P' j j' hj hj'
  have := hj.1.isClosedSubgroup.mono
  have := hj'.1.isClosedSubgroup.mono
  have hrep : (Dynamic.parabolic (χ ≫ i)).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, hPj⟩
  have hrep' : (Dynamic.parabolic (χ' ≫ i)).IsRepresentedBy j' :=
    ⟨Over.mono_of_mono_left _, hPj'⟩
  have hf := Dynamic.parabolicTorusFactor_comp i χ hrep
  have hf' := Dynamic.parabolicTorusFactor_comp i χ' hrep'
  set f := Dynamic.parabolicTorusFactor i χ hrep
  set f' := Dynamic.parabolicTorusFactor i χ' hrep'
  have hfe : (f ≫ e.hom) ≫ j' = i ≫ (G.innerIso h).hom := by
    rw [Category.assoc, ← hje, ← Category.assoc, hf]
  obtain ⟨p, eT, hp⟩ := htorus k G hG P' j' hj' T T (i ≫ (G.innerIso h).hom) i
    (hi.comp_iso (G.innerIso h)) hi (f ≫ e.hom) f' hfe hf'
  have hn : i ≫ (G.innerIso ((p ≫ j'.hom.hom) * h)).hom = eT.hom ≫ i := by
    calc i ≫ (G.innerIso ((p ≫ j'.hom.hom) * h)).hom
        = (i ≫ (G.innerIso h).hom) ≫ (G.innerIso (p ≫ j'.hom.hom)).hom := by
          rw [innerIso_mul_hom, Category.assoc]
      _ = ((f ≫ e.hom) ≫ (P'.innerIso p).hom) ≫ j' := by
          rw [← hfe]
          simp only [Category.assoc, innerIso_hom_comp]
      _ = eT.hom ≫ i := by
          rw [hp, Category.assoc, hf']
  let σ : T ≅ T :=
    { hom := Additive.ofMul eT.hom
      inv := Additive.ofMul eT.inv
      hom_inv_id := congrArg Additive.ofMul eT.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul eT.inv_hom_id }
  refine ⟨(p ≫ j'.hom.hom) * h, ⟨σ, hn⟩, ?_⟩
  rw [← hPj, ← hPj']
  refine range_eq_comap_of_comp_eq _ (e ≪≫ P'.innerIso p) ?_
  rw [innerIso_mul_hom, ← Category.assoc, hje, Iso.trans_hom, Category.assoc, Category.assoc,
    innerIso_hom_comp]

end Conjugation

/-! ### The surjectivity reduction -/

section Field

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- **Rational representatives for a normalizing point acting through one automorphism.**
Let `g` be a point of the torus normalizer over a test scheme `U` that acts on `T` through the
automorphism `σ` after every refinement. Then some rational normalizing point `n` has
`n|_U⁻¹ * g` in the torus centralizer over `U`. -/
theorem exists_inv_mul_mem_torusCentralizer
    (hgen : GenericMinimalParabolicStatement.{u})
    (hconj : MinimalParabolicConjugacyStatement.{u})
    (htorus : MinimalParabolicSplitTorusConjugacyStatement.{u})
    (hcent : GenericCentralizerStatement.{u})
    (hself : ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j → (SubgroupFunctor.range j).normalizer = SubgroupFunctor.range j)
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    {U : Over (Spec (CommRingCat.of k))} {g : U ⟶ G.X}
    (hg : g ∈ (torusNormalizer i).carrier U) (σ : T ≅ T)
    (hσ : ∀ (V : Over (Spec (CommRingCat.of k))) (a : V ⟶ U) (t : V ⟶ T.X),
      (a ≫ g) * (t ≫ i.hom.hom) * (a ≫ g)⁻¹ =
        (t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ i.hom.hom) :
    ∃ n : normalizerPoints i,
      (G.constantPoint n U)⁻¹ * g ∈ (torusCentralizer i).carrier U := by
  have := hG.isAffineHom
  have := hG.smooth
  have hT : IsSplitTorus T.toGrp := hi.1.1
  -- a cocharacter `ν` with `ν` and `ν ≫ σ` both generic
  let r : Set (characterLattice T) :=
    relativeRoots i ∪ (fun α => σ.hom ≫ α) '' relativeRoots i
  have hr : r.Finite :=
    (hT.finite_relativeRoots i).union ((hT.finite_relativeRoots i).image _)
  have hr0 : ∀ α ∈ r, α ≠ 0 := by
    rintro α (hα | ⟨β, hβ, rfl⟩)
    · exact hα.1
    · intro h0
      apply hβ.1
      exact (cancel_epi σ.hom).mp (by rw [comp_zero]; exact h0)
  obtain ⟨ν, hν⟩ := hT.exists_pairings_ne_zero r hr hr0
  have hgenν : IsGenericCocharacter i ν := fun α hα => hν α (Or.inl hα)
  have hgenν' : IsGenericCocharacter i (ν ≫ σ.hom) := fun α hα => by
    have h := hν (σ.hom ≫ α) (Or.inr ⟨α, hα, rfl⟩)
    rw [latticePairing_apply] at h
    rwa [latticePairing_apply, Category.assoc]
  -- the two minimal parabolics and a rational normalizing point conjugating them
  obtain ⟨P, j, hj, hPj⟩ :=
    isMinimalParabolicFunctor_iff_exists.mp (hgen k G hG T i hi ν hgenν)
  obtain ⟨P', j', hj', hPj'⟩ :=
    isMinimalParabolicFunctor_iff_exists.mp (hgen k G hG T i hi (ν ≫ σ.hom) hgenν')
  obtain ⟨n, hn, hnP⟩ := exists_normalizingPoint_comap_eq hconj htorus hG i hi
    (CommGroupScheme.groupHom ν) (CommGroupScheme.groupHom (ν ≫ σ.hom)) hj hj' hPj hPj'
  -- `g` conjugates `ν ≫ i` into `ν ≫ σ ≫ i`
  have hgχ : ConjugatesCocharacter g (CommGroupScheme.groupHom ν ≫ i)
      (CommGroupScheme.groupHom (ν ≫ σ.hom) ≫ i) := by
    intro V a s
    have h := hσ V a (s ≫ (CommGroupScheme.groupHom ν).hom.hom)
    have e1 : CommGroupScheme.groupHom (ν ≫ σ.hom) =
        CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom σ.hom := rfl
    simp only [e1, Grp.comp_hom_hom, Category.assoc] at h ⊢
    exact h
  -- `n⁻¹ g` normalizes the parabolic, hence lies in it
  have hmP := constantPoint_inv_mul_mem_normalizer n hnP hgχ
  rw [← hPj, hself P j hj.1, hPj] at hmP
  have hmN : (G.constantPoint n U)⁻¹ * g ∈ (torusNormalizer i).carrier U :=
    ((torusNormalizer i).carrier U).mul_mem
      (((torusNormalizer i).carrier U).inv_mem (normalizerPointsRestrict i U ⟨n, hn⟩).2) hg
  have hrange : SubgroupFunctor.range i ≤ Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) :=
    (range_le_torusCentralizer i).trans (torusCentralizer_le_dynamicCentralizer i _)
  have hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) ≤ torusCentralizer i :=
    (hcent k G hG T i hi ν hgenν).le
  exact ⟨⟨n, hn⟩, mem_torusCentralizer_of_mem_parabolic i _ hrange hZ hmN hmP⟩

/-- **Surjectivity of `N(k)/Z(k) → N(U)/Z(U)` from rigidity.** If every point of the torus
normalizer over `U` acts on `T` through one automorphism of `T`, then restriction
`relativeWeylGroup i → pointWeylGroup i U` is surjective. -/
theorem relativeWeylGroupRestrict_surjective_of_rigid
    (hgen : GenericMinimalParabolicStatement.{u})
    (hconj : MinimalParabolicConjugacyStatement.{u})
    (htorus : MinimalParabolicSplitTorusConjugacyStatement.{u})
    (hcent : GenericCentralizerStatement.{u})
    (hself : ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
      IsParabolicSubgroup j → (SubgroupFunctor.range j).normalizer = SubgroupFunctor.range j)
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (U : Over (Spec (CommRingCat.of k)))
    (hrig : ∀ g ∈ (torusNormalizer i).carrier U, ∃ σ : T ≅ T,
      ∀ (V : Over (Spec (CommRingCat.of k))) (a : V ⟶ U) (t : V ⟶ T.X),
        (a ≫ g) * (t ≫ i.hom.hom) * (a ≫ g)⁻¹ =
          (t ≫ (CommGroupScheme.groupHom σ.hom).hom.hom) ≫ i.hom.hom) :
    Function.Surjective (relativeWeylGroupRestrict i U) := by
  intro w
  induction w using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨σ, hσ⟩ := hrig g g.2
    obtain ⟨n, hn⟩ := exists_inv_mul_mem_torusCentralizer hgen hconj htorus hcent hself hG i hi
      g.2 σ hσ
    refine ⟨QuotientGroup.mk n, ?_⟩
    rw [relativeWeylGroupRestrict_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hn

end Field

end RelativeWeylSurjective

end Langlands.GroupScheme
