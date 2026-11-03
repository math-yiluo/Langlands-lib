import Langlands.GroupScheme.Rational.RelativeWeylCoxeterStatement
import Langlands.GroupScheme.Rational.RootReflectionExistenceStatement
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter
import Langlands.GroupScheme.Rational.PositiveRootInduction
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Mathlib.GroupTheory.Coxeter.Length

/-! # Transporting a Coxeter system from the actual root pairing to `N(k)/Z(k)` -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan
open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

namespace Langlands.GroupScheme

/-! ### Kernel centralizers and normalizing points in dynamic centralizers -/

section Scheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

/-- A point centralizing the scheme-theoretic kernel of a character `a` centralizes every
cocharacter `ζ` with `⟨a, ζ⟩ = 0`, since such a cocharacter factors through that kernel. -/
theorem RelativeRoot.kernelCentralizer_le_dynamicCentralizer {a : characterLattice T}
    {ζ : cocharacterLattice T} (h : latticePairing T a ζ = 0) :
    RelativeRoot.kernelCentralizer i a ≤
      Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) := by
  intro U g hg
  rw [RelativeRoot.mem_kernelCentralizer] at hg
  rw [Dynamic.mem_centralizer]
  have hζa : ζ ≫ a = 0 := by
    apply (gmEndEquiv k).injective
    rw [map_zero]
    exact h
  let t := snd U (Gm (Spec (CommRingCat.of k))).X
  let x : U ⊗ (Gm (Spec (CommRingCat.of k))).X ⟶ T.X :=
    t ≫ (CommGroupScheme.groupHom ζ).hom.hom
  have hx : x ≫ (CommGroupScheme.groupHom a).hom.hom = 1 := by
    change (t ≫ (CommGroupScheme.groupHom ζ).hom.hom) ≫ (CommGroupScheme.groupHom a).hom.hom = 1
    rw [← comp_groupHom_comp, hζa, comp_groupHom_zero]
  let c := (kernelPointsEquiv (CommGroupScheme.groupHom a)
    (U ⊗ (Gm (Spec (CommRingCat.of k))).X)).symm ⟨x, hx⟩
  have hc : c ≫ (kernelι (CommGroupScheme.groupHom a)).hom.hom = x :=
    congrArg Subtype.val ((kernelPointsEquiv _ _).apply_symm_apply ⟨x, hx⟩)
  have hcomm := hg _ (fst U (Gm (Spec (CommRingCat.of k))).X) c
  have hci : c ≫ (RelativeRoot.characterKernelι a ≫ i).hom.hom =
      t ≫ (CommGroupScheme.groupHom ζ ≫ i).hom.hom := by
    simp only [Grp.comp_hom_hom]
    rw [← Category.assoc, hc, Category.assoc]
  rw [hci] at hcomm
  simp only [Dynamic.orbit]
  rw [← hcomm.eq, mul_inv_cancel_right]

variable [Mono i.hom.hom.left]

/-- A normalizing rational point lying in the dynamic centralizer of a cocharacter `ζ`
fixes `ζ` under its automorphism of the torus. -/
theorem cocharacterAut_normalizingAut_eq_of_mem_dynamicCentralizer
    (n : normalizerPoints i) {ζ : cocharacterLattice T}
    (hn : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈
      (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    cocharacterAut (normalizingAut i n) ζ = ζ := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  let σ := normalizingAut i n
  have hσ := isNormalizingPoint_normalizingAut i n
  let U₀ := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let t := snd U₀ (Gm (Spec (CommRingCat.of k))).X
  let c := fst U₀ (Gm (Spec (CommRingCat.of k))).X ≫
    (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
  have hc : c = G.constantPoint n (U₀ ⊗ (Gm (Spec (CommRingCat.of k))).X) := by
    rw [← G.constantPoint_naturality n (fst U₀ (Gm (Spec (CommRingCat.of k))).X)]
    exact congrArg (fst U₀ (Gm (Spec (CommRingCat.of k))).X ≫ ·) (G.constantPoint_self n).symm
  have hconj : ∀ y : U₀ ⊗ (Gm (Spec (CommRingCat.of k))).X ⟶ T.X,
      c * (y ≫ i.hom.hom) * c⁻¹ =
        y ≫ (CommGroupScheme.groupHom σ.hom).hom.hom ≫ i.hom.hom := by
    intro y
    have h := congrArg (fun φ : T.toGrp ⟶ G => y ≫ φ.hom.hom) hσ
    simp only [Grp.comp_hom_hom] at h
    rw [← Category.assoc, comp_innerIso_hom, ← hc] at h
    exact h
  let y := t ≫ (CommGroupScheme.groupHom ζ).hom.hom
  have horbit : (y ≫ i.hom.hom) * c * (y ≫ i.hom.hom)⁻¹ = c := by
    rw [Dynamic.mem_centralizer] at hn
    simp only [Dynamic.orbit, Grp.comp_hom_hom] at hn
    simpa only [y, Category.assoc] using hn
  have hfix : c * (y ≫ i.hom.hom) * c⁻¹ = y ≫ i.hom.hom := by
    rw [mul_inv_eq_iff_eq_mul]
    rw [mul_inv_eq_iff_eq_mul] at horbit
    exact horbit.symm
  have key : t ≫ (CommGroupScheme.groupHom (ζ ≫ σ.hom)).hom.hom =
      t ≫ (CommGroupScheme.groupHom ζ).hom.hom := by
    rw [comp_groupHom_comp]
    apply (cancel_mono i.hom.hom).1
    rw [Category.assoc, ← hconj, hfix]
  rw [cocharacterAut_apply]
  apply CommGroupScheme.hom_ext_points
  intro U x
  let s : U ⟶ U₀ ⊗ (Gm (Spec (CommRingCat.of k))).X :=
    lift (Over.homMk U.hom (by simp [U₀])) x
  have hs : s ≫ t = x := lift_snd _ _
  rw [← hs, Category.assoc, Category.assoc, key]

/-- A normalizing rational point in the dynamic centralizer of `ζ` preserves the pairing of
every character with `ζ`. -/
theorem latticePairing_weylAction_of_mem_dynamicCentralizer
    (n : normalizerPoints i) {ζ : cocharacterLattice T}
    (hn : (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) ∈
      (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (χ : characterLattice T) :
    latticePairing T (weylAction i n χ) ζ = latticePairing T χ ζ := by
  conv_lhs => rw [← cocharacterAut_normalizingAut_eq_of_mem_dynamicCentralizer i n hn]
  rw [weylAction_apply, ← characterAut_apply, latticePairing_characterAut_cocharacterAut]

end Scheme

/-! ### Transport of Coxeter lengths -/

section CoxeterTransport

variable {B B' W H : Type*} [Group W] [Group H] {M : CoxeterMatrix B} {M' : CoxeterMatrix B'}

/-- A homomorphism sending each simple generator of `cs` to a simple generator of `cs'`
does not increase Coxeter length. -/
theorem coxeterLength_map_le (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' H)
    (e : W →* H) (σ : B → B') (he : ∀ b, e (cs.simple b) = cs'.simple (σ b)) (w : W) :
    cs'.length (e w) ≤ cs.length w := by
  have key : ∀ ω : List B, e (cs.wordProd ω) = cs'.wordProd (ω.map σ) := by
    intro ω
    induction ω with
    | nil => simp [CoxeterSystem.wordProd_nil]
    | cons b ω ih =>
      rw [CoxeterSystem.wordProd_cons, map_mul, he, ih, List.map_cons,
        CoxeterSystem.wordProd_cons]
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  rw [key, hω.eq]
  exact (cs'.length_wordProd_le _).trans (by simp)

/-- A group isomorphism matching simple generators through a bijection of labels
preserves Coxeter length. -/
theorem coxeterLength_map_eq (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' H)
    (e : W ≃* H) (σ : B ≃ B') (he : ∀ b, e (cs.simple b) = cs'.simple (σ b)) (w : W) :
    cs'.length (e w) = cs.length w := by
  refine le_antisymm (coxeterLength_map_le cs cs' e.toMonoidHom σ he w) ?_
  have he' : ∀ b', e.symm (cs'.simple b') = cs.simple (σ.symm b') := by
    intro b'
    rw [MulEquiv.symm_apply_eq, he, Equiv.apply_symm_apply]
  simpa using coxeterLength_map_le cs' cs e.symm.toMonoidHom σ.symm he' (e w)

end CoxeterTransport

/-! ### Reflection data in the actual torus -/

section ReflectionData

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
  [IsAffineHom G.X.hom] [Mono i.hom.hom.left]

open RelativeRootSystem

/-- The actual Weyl action preserves the actual relative roots. -/
theorem schemeWeylCharacterAction_mem_relativeRoots (w : relativeWeylGroup i)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i) :
    schemeWeylCharacterAction i w χ ∈ relativeRoots i := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  exact weylAction_mapsTo_relativeRoots i n hχ

/-- On a root vector, the action on the root span is the action on characters. -/
theorem relativeWeylAction_rootVector (w : relativeWeylGroup i) (β : relativeRoots i) :
    relativeWeylAction i w (rootVector i β) =
      rootVector i ⟨schemeWeylCharacterAction i w β.val,
        schemeWeylCharacterAction_mem_relativeRoots w β.property⟩ := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  exact relativeWeylAction_mk_toRat i n β.property

omit [Mono i.hom.hom.left] in
/-- For a split torus, a multiple of a root vector is a root vector exactly when the
same multiple holds for the characters. -/
theorem nsmul_rootVector_eq_iff (hT : IsSplitTorus T.toGrp) (n : ℕ) (β γ : relativeRoots i) :
    n • rootVector i β = rootVector i γ ↔ n • β.val = γ.val := by
  constructor
  · intro hn
    apply hT.character_toRat_injective
    have := congrArg Subtype.val hn
    simpa [rootVector, map_nsmul] using this
  · intro hn
    apply Subtype.ext
    simp [rootVector, ← hn, map_nsmul]

theorem HasRelativeRootSystem.relativeWeylAction_injective (h : HasRelativeRootSystem i) :
    Function.Injective (relativeWeylAction i) := by
  obtain ⟨_, _, _, _, _, _, _, _, hf⟩ := h
  exact hf

/-- For a generic cocharacter, a root whose negative is not positive is positive. -/
theorem mem_positiveRelativeRoots_of_neg_not_mem (h : HasRelativeRootSystem i)
    (hT : IsSplitTorus T.toGrp) {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    {x : characterLattice T} (hx : x ∈ relativeRoots i)
    (hneg : -x ∉ positiveRelativeRoots i ν) : x ∈ positiveRelativeRoots i ν := by
  refine ⟨hx, ?_⟩
  rcases lt_trichotomy (latticePairing T x ν) 0 with hlt | heq | hgt
  · refine absurd ⟨h.neg_mem_relativeRoots i hT hx, ?_⟩ hneg
    rw [map_neg, LinearMap.neg_apply]
    omega
  · exact absurd heq (hν x hx)
  · exact hgt

namespace RelativeRootReflectionData

variable (D : RelativeRootReflectionData i)

include D in
/-- A positive multiple `n • γ` of an actual root that is again an actual root has
`n ≤ 2`, by pairing with the coroot of the multiple. -/
theorem eq_two_of_nsmul_eq {γ β : relativeRoots i} {n : ℕ} (hn : 2 ≤ n)
    (h : n • γ.val = β.val) : n = 2 := by
  have h2 := congrArg (fun χ => latticePairing T χ (D.coroot β)) h
  simp only [map_nsmul, LinearMap.smul_apply, D.pair_self, nsmul_eq_mul] at h2
  have hdvd : (n : ℤ) ∣ 2 := ⟨latticePairing T γ.val (D.coroot β), h2.symm⟩
  have := Int.le_of_dvd two_pos hdvd
  omega

/-- The chosen representative of a root lies in the standard Levi of every root set
containing that root, when it centralizes the kernel of the root. -/
theorem representative_mem_standardLeviPoints
    (hker : ∀ a : relativeRoots i, (D.representative a).val ∈
      (RelativeRoot.kernelCentralizer i a.val).carrier (Over.mk (𝟙 _)))
    (ν : cocharacterLattice T) {J : Set (characterLattice T)} {α : relativeRoots i}
    (hα : α.val ∈ J) :
    (D.representative α).val ∈ standardLeviPoints i ν J := by
  rw [standardLeviPoints, mem_standardLevi]
  intro ζ hζ
  exact RelativeRoot.kernelCentralizer_le_dynamicCentralizer i (hζ.2.1 α.val hα) _ (hker α)

variable (hT : IsSplitTorus T.toGrp) (hfin : (relativeRoots i).Finite)

/-- Under the relative-root-system hypothesis, the reflections of the constructed pairing
generate the image of the whole actual relative Weyl group. -/
theorem weylGroup_map_eq_range (h : HasRelativeRootSystem i) :
    (D.rootPairing hT hfin).weylGroup.map
        (RootPairing.Equiv.weightHom (D.rootPairing hT hfin)) =
      (relativeWeylAction i).range := by
  apply le_antisymm
  · rw [D.weylGroup_image, Subgroup.closure_le]
    rintro _ ⟨α, rfl⟩
    exact ⟨_, rfl⟩
  · obtain ⟨J, _, P', _, _, _, hroots, hW, _⟩ := h
    have := hfin.to_subtype
    set P := D.rootPairing hT hfin
    have hrange : Set.range P'.root = Set.range P.root := by
      apply (Set.image_injective.mpr Subtype.val_injective)
      rw [hroots, D.rootPairing_root_image]
    rw [← hW, ← MonoidHom.domRestrict_range, RootPairing.range_weylGroup_weightHom,
      ← MonoidHom.domRestrict_range, RootPairing.range_weylGroup_weightHom, Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨α, hα⟩ : P'.root j ∈ Set.range P.root := hrange ▸ Set.mem_range_self j
    have hcoroot : P'.coroot' j = P.coroot' α := by
      apply Module.Dual.eq_of_preReflection_mapsTo (x := P.root α) (Set.finite_range P.root)
        (span_range_rootVector i)
      · rw [hα]
        exact P'.coroot_root_two j
      · rw [← hrange, hα]
        exact P'.mapsTo_reflection_root j
      · exact P.coroot_root_two α
      · exact P.mapsTo_reflection_root α
    have hrefl : P'.reflection j = P.reflection α := by
      ext x
      rw [RootPairing.reflection_apply, RootPairing.reflection_apply, hcoroot, ← hα]
    rw [hrefl]
    exact Subgroup.subset_closure (Set.mem_range_self α)

theorem weightHom_domRestrict_injective :
    Function.Injective ((RootPairing.Equiv.weightHom (D.rootPairing hT hfin)).domRestrict
      (D.rootPairing hT hfin).weylGroup) :=
  fun _ _ hab => Subtype.ext (RootPairing.Equiv.weightHom_injective _ hab)

/-- The Weyl group of the constructed pairing, identified with the actual relative
Weyl group through their common faithful action on the root span. -/
def weylGroupEquiv (h : HasRelativeRootSystem i) :
    (D.rootPairing hT hfin).weylGroup ≃* relativeWeylGroup i :=
  (MonoidHom.ofInjective (D.weightHom_domRestrict_injective hT hfin)).trans
    ((MulEquiv.subgroupCongr (by
        rw [MonoidHom.domRestrict_range]
        exact D.weylGroup_map_eq_range hT hfin h)).trans
      (MonoidHom.ofInjective h.relativeWeylAction_injective).symm)

theorem relativeWeylAction_weylGroupEquiv (h : HasRelativeRootSystem i)
    (w : (D.rootPairing hT hfin).weylGroup) :
    relativeWeylAction i (D.weylGroupEquiv hT hfin h w) =
      RootPairing.Equiv.weightHom (D.rootPairing hT hfin) w.val := by
  change relativeWeylAction i ((MonoidHom.ofInjective h.relativeWeylAction_injective).symm _) = _
  rw [← MonoidHom.ofInjective_apply h.relativeWeylAction_injective, MulEquiv.apply_symm_apply]
  rfl

theorem weylGroupEquiv_ofIdx (h : HasRelativeRootSystem i) (α : relativeRoots i) :
    D.weylGroupEquiv hT hfin h (RootPairing.weylGroup.ofIdx (D.rootPairing hT hfin) α) =
      QuotientGroup.mk (D.representative α) := by
  apply h.relativeWeylAction_injective
  rw [relativeWeylAction_weylGroupEquiv, ← D.reflection_eq_relativeWeylAction hT hfin α]
  exact RootPairing.Equiv.reflection_weightEquiv _ α

theorem smul_root (h : HasRelativeRootSystem i) (w : (D.rootPairing hT hfin).weylGroup)
    (β : relativeRoots i) :
    w • (D.rootPairing hT hfin).root β =
      rootVector i ⟨schemeWeylCharacterAction i (D.weylGroupEquiv hT hfin h w) β.val,
        schemeWeylCharacterAction_mem_relativeRoots _ β.property⟩ := by
  rw [← relativeWeylAction_rootVector, relativeWeylAction_weylGroupEquiv]
  rfl

theorem corootFunctional_smul_root (h : HasRelativeRootSystem i) (ζ : cocharacterLattice T)
    (w : (D.rootPairing hT hfin).weylGroup) (β : relativeRoots i) :
    corootFunctional i ζ (w • (D.rootPairing hT hfin).root β) =
      (latticePairing T (schemeWeylCharacterAction i (D.weylGroupEquiv hT hfin h w) β.val) ζ :
        ℚ) := by
  rw [D.smul_root hT hfin h, corootFunctional_rootVector]

/-- A root index lies in the base of `corootFunctional i ν` exactly when its character
is an actual simple relative root. -/
theorem mem_baseOf_iff (ν : cocharacterLattice T) (α : relativeRoots i) :
    α ∈ IsAddIndecomposable.baseOf (D.rootPairing hT hfin).root
        (corootFunctional i ν : relativeRootSpan i →+ ℚ) ↔
      α.val ∈ simpleRelativeRoots i ν := by
  have hf (j : relativeRoots i) :
      (corootFunctional i ν : relativeRootSpan i →+ ℚ) ((D.rootPairing hT hfin).root j) =
        (latticePairing T j.val ν : ℚ) :=
    corootFunctional_rootVector i ν j
  constructor
  · rintro ⟨hpos, hind⟩
    have hpos' : 0 < latticePairing T α.val ν := by
      have : (0 : ℚ) < latticePairing T α.val ν := by
        rw [← hf]
        exact hpos
      exact_mod_cast this
    refine ⟨⟨α.property, hpos'⟩, ?_⟩
    rintro ⟨β, hβ, γ, hγ, heq⟩
    have hβ' : (0 : ℚ) < latticePairing T β ν := by exact_mod_cast hβ.2
    have hγ' : (0 : ℚ) < latticePairing T γ ν := by exact_mod_cast hγ.2
    have hsum : (D.rootPairing hT hfin).root α =
        (D.rootPairing hT hfin).root ⟨β, hβ.1⟩ + (D.rootPairing hT hfin).root ⟨γ, hγ.1⟩ := by
      apply Subtype.ext
      change toRat α.val = toRat β + toRat γ
      rw [heq, map_add]
    rcases hind ⟨β, hβ.1⟩ (by rw [Set.mem_ofPred_eq, hf]; exact hβ')
        ⟨γ, hγ.1⟩ (by rw [Set.mem_ofPred_eq, hf]; exact hγ') hsum with h0 | h0
    · exact (D.rootPairing hT hfin).ne_zero _ h0
    · exact (D.rootPairing hT hfin).ne_zero _ h0
  · intro hα
    refine ⟨?_, fun j hj l hl heq => ?_⟩
    · rw [Set.mem_ofPred_eq, hf]
      exact_mod_cast hα.1.2
    · exfalso
      apply hα.2
      have hj' : 0 < latticePairing T j.val ν := by
        have : (0 : ℚ) < latticePairing T j.val ν := by
          rw [← hf]
          exact hj
        exact_mod_cast this
      have hl' : 0 < latticePairing T l.val ν := by
        have : (0 : ℚ) < latticePairing T l.val ν := by
          rw [← hf]
          exact hl
        exact_mod_cast this
      refine ⟨j.val, ⟨j.property, hj'⟩, l.val, ⟨l.property, hl'⟩, ?_⟩
      apply hT.character_toRat_injective
      rw [map_add]
      exact congrArg Subtype.val heq

/-- The base of the constructed pairing, relabelled by the actual simple relative roots. -/
def baseEquiv (ν : cocharacterLattice T) :
    IsAddIndecomposable.baseOf (D.rootPairing hT hfin).root
        (corootFunctional i ν : relativeRootSpan i →+ ℚ) ≃
      SimpleRoot i ν where
  toFun b := ⟨b.val.val, (D.mem_baseOf_iff hT hfin ν b.val).1 b.property⟩
  invFun a := ⟨⟨a.val, a.property.1.1⟩, (D.mem_baseOf_iff hT hfin ν _).2 a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

include D in
/-- A simple relative root is reduced: were it `n • β`, then `n = 2` and it would be the sum
`β + β` of two positive roots. -/
theorem mem_reducedPositiveRelativeRoots_of_mem_simple {ν : cocharacterLattice T}
    {a : characterLattice T} (ha : a ∈ simpleRelativeRoots i ν) :
    a ∈ reducedPositiveRelativeRoots i ν := by
  refine ⟨ha.1, fun n hn β hβ heq => ?_⟩
  have h2 := D.eq_two_of_nsmul_eq (γ := ⟨β, hβ⟩) (β := ⟨a, ha.1.1⟩) hn heq
  subst h2
  have hpos : β ∈ positiveRelativeRoots i ν := by
    refine ⟨hβ, ?_⟩
    have := ha.1.2
    rw [← heq] at this
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
    omega
  exact ha.2 ⟨β, hpos, β, hpos, by rw [← heq, two_nsmul]⟩

/-- **Transport of the Coxeter structure.** Let `D` be integral reflection data whose
representatives centralize the kernels of their roots, under the relative-root-system
hypothesis and for a generic cocharacter `ν`. Suppose the Weyl group of the constructed
pairing `D.rootPairing` carries a Coxeter system on the base of `corootFunctional i ν`, with
the simple reflections, the length formula and the descent criterion of
`RootPairingWeylCoxeterStatement`. Then the actual relative Weyl group has a Coxeter system
realizing the relative root action. -/
theorem hasRelativeWeylCoxeterSystem_of_rootPairing (h : HasRelativeRootSystem i)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hker : ∀ a : relativeRoots i, (D.representative a).val ∈
      (RelativeRoot.kernelCentralizer i a.val).carrier (Over.mk (𝟙 _)))
    (Mx : CoxeterMatrix (IsAddIndecomposable.baseOf (D.rootPairing hT hfin).root
      (corootFunctional i ν : relativeRootSpan i →+ ℚ)))
    (cs : CoxeterSystem Mx (D.rootPairing hT hfin).weylGroup)
    (hsimple : ∀ b, cs.simple b = RootPairing.weylGroup.ofIdx (D.rootPairing hT hfin) b)
    (hlength : ∀ w, cs.length w = Set.ncard {j |
      0 < corootFunctional i ν ((D.rootPairing hT hfin).root j) ∧
      (∀ n : ℕ, 2 ≤ n → ∀ j',
        n • (D.rootPairing hT hfin).root j' ≠ (D.rootPairing hT hfin).root j) ∧
      corootFunctional i ν (w • (D.rootPairing hT hfin).root j) < 0})
    (hdescent : ∀ w b, cs.length w < cs.length (w * cs.simple b) ↔
      0 < corootFunctional i ν (w • (D.rootPairing hT hfin).root b)) :
    HasRelativeWeylCoxeterSystem i ν := by
  classical
  set P := D.rootPairing hT hfin
  set φ := D.weylGroupEquiv hT hfin h
  set σ := D.baseEquiv hT hfin ν
  let cs' := (cs.reindex σ).map φ
  have hsimple' (a : SimpleRoot i ν) :
      cs'.simple a = QuotientGroup.mk (D.representative ⟨a.1, a.2.1.1⟩) := by
    change φ (cs.simple (σ.symm a)) = _
    rw [hsimple]
    exact D.weylGroupEquiv_ofIdx hT hfin h _
  have hlen' (w : P.weylGroup) : cs'.length (φ w) = cs.length w :=
    coxeterLength_map_eq cs cs' φ σ (fun b => by
      change φ (cs.simple b) = φ (cs.simple (σ.symm (σ b)))
      rw [Equiv.symm_apply_apply]) w
  have hf (w : P.weylGroup) (β : relativeRoots i) :
      corootFunctional i ν (w • P.root β) =
        (latticePairing T (schemeWeylCharacterAction i (φ w) β.val) ν : ℚ) :=
    D.corootFunctional_smul_root hT hfin h ν w β
  have hf₀ (β : relativeRoots i) :
      corootFunctional i ν (P.root β) = (latticePairing T β.val ν : ℚ) :=
    corootFunctional_rootVector i ν β
  have hpairing_neg (x : characterLattice T) (ζ : cocharacterLattice T) :
      latticePairing T (-x) ζ = -latticePairing T x ζ := by
    rw [map_neg, LinearMap.neg_apply]
  -- Clause 1: the reflection formula.
  have c1 (a : SimpleRoot i ν) (χ : characterLattice T) :
      schemeWeylCharacterAction i (cs'.simple a) χ =
        χ - latticePairing T χ (D.coroot ⟨a.1, a.2.1.1⟩) • a.1 := by
    rw [hsimple', schemeWeylCharacterAction_mk, D.action]
  -- Clause 3: the descent criterion.
  have c3 (w : relativeWeylGroup i) (a : SimpleRoot i ν) :
      cs'.length w < cs'.length (w * cs'.simple a) ↔
        schemeWeylCharacterAction i w a.1 ∈ positiveRelativeRoots i ν := by
    obtain ⟨w, rfl⟩ := φ.surjective w
    have hmul : φ w * cs'.simple a = φ (w * cs.simple (σ.symm a)) := by
      rw [map_mul]
      rfl
    rw [hmul, hlen', hlen', hdescent, hf, Int.cast_pos]
    exact ⟨fun hp => ⟨schemeWeylCharacterAction_mem_relativeRoots _ a.2.1.1, hp⟩, And.right⟩
  -- Clause 4: the length formula.
  have c4 (w : relativeWeylGroup i) :
      cs'.length w = (relativeInversionSet i ν w).ncard := by
    obtain ⟨w, rfl⟩ := φ.surjective w
    have hset : relativeInversionSet i ν (φ w) = Subtype.val '' {j |
        0 < corootFunctional i ν (P.root j) ∧
        (∀ n : ℕ, 2 ≤ n → ∀ j', n • P.root j' ≠ P.root j) ∧
        corootFunctional i ν (w • P.root j) < 0} := by
      ext χ
      constructor
      · rintro ⟨⟨⟨hroot, hpos⟩, hred⟩, -, hneg⟩
        refine ⟨⟨χ, hroot⟩, ⟨?_, fun n hn j' heq => hred n hn j'.val j'.property
          ((nsmul_rootVector_eq_iff hT n _ _).1 heq), ?_⟩, rfl⟩
        · rw [hf₀, Int.cast_pos]
          exact hpos
        · rw [hf, Int.cast_lt_zero]
          change latticePairing T (schemeWeylCharacterAction i (φ w) χ) ν < 0
          rw [hpairing_neg] at hneg
          omega
      · rintro ⟨β, ⟨hpos, hred, hneg⟩, rfl⟩
        rw [hf₀, Int.cast_pos] at hpos
        rw [hf, Int.cast_lt_zero] at hneg
        refine ⟨⟨⟨β.property, hpos⟩, fun n hn γ hγ heq => hred n hn ⟨γ, hγ⟩
          ((nsmul_rootVector_eq_iff hT n _ _).2 heq)⟩,
          h.neg_mem_relativeRoots i hT (schemeWeylCharacterAction_mem_relativeRoots _ β.property),
          ?_⟩
        rw [hpairing_neg]
        omega
    rw [hlen', hlength, hset, Set.ncard_image_of_injective _ Subtype.val_injective]
  -- Clause 2: a simple reflection permutes the other positive roots.
  have hinv_simple (a : SimpleRoot i ν) :
      relativeInversionSet i ν (cs'.simple a) = {a.1} := by
    have hmem : a.1 ∈ relativeInversionSet i ν (cs'.simple a) := by
      refine ⟨D.mem_reducedPositiveRelativeRoots_of_mem_simple a.2, ?_⟩
      rw [c1, D.pair_self ⟨a.1, a.2.1.1⟩]
      have : -(a.1 - (2 : ℤ) • a.1) = a.1 := by
        rw [two_zsmul]
        abel
      rw [this]
      exact a.2.1
    have hcard : (relativeInversionSet i ν (cs'.simple a)).ncard = 1 := by
      rw [← c4, CoxeterSystem.length_simple]
    obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 hcard
    rw [hx] at hmem ⊢
    rw [Set.mem_singleton_iff.1 hmem]
  have hreduced (a : SimpleRoot i ν) {γ : characterLattice T}
      (hγ : γ ∈ reducedPositiveRelativeRoots i ν) (hne : γ ≠ a.1) :
      schemeWeylCharacterAction i (cs'.simple a) γ ∈ positiveRelativeRoots i ν := by
    apply mem_positiveRelativeRoots_of_neg_not_mem h hT hν
      (schemeWeylCharacterAction_mem_relativeRoots _ hγ.1.1)
    intro hneg
    have hmem : γ ∈ relativeInversionSet i ν (cs'.simple a) := ⟨hγ, hneg⟩
    rw [hinv_simple] at hmem
    exact hne hmem
  have c2 (a : SimpleRoot i ν) (β : characterLattice T) (hβ : β ∈ positiveRelativeRoots i ν)
      (hne : β ≠ a.1) (hne2 : β ≠ 2 • a.1) :
      schemeWeylCharacterAction i (cs'.simple a) β ∈ positiveRelativeRoots i ν := by
    by_cases hred : ∀ n : ℕ, 2 ≤ n → ∀ γ ∈ relativeRoots i, n • γ ≠ β
    · exact hreduced a ⟨hβ, hred⟩ hne
    push Not at hred
    obtain ⟨n, hn, γ, hγ, rfl⟩ := hred
    have h2 := D.eq_two_of_nsmul_eq (γ := ⟨γ, hγ⟩) (β := ⟨_, hβ.1⟩) hn rfl
    subst h2
    have hγpos : γ ∈ positiveRelativeRoots i ν := by
      refine ⟨hγ, ?_⟩
      have := hβ.2
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] at this
      omega
    have hγred : γ ∈ reducedPositiveRelativeRoots i ν := by
      refine ⟨hγpos, fun m hm δ hδ heq => ?_⟩
      have := D.eq_two_of_nsmul_eq (γ := ⟨δ, hδ⟩) (β := ⟨_, hβ.1⟩) (n := 2 * m) (by omega)
        (by rw [mul_smul, heq])
      omega
    have hγa : γ ≠ a.1 := fun he => hne2 (by rw [he])
    have himage := hreduced a hγred hγa
    refine ⟨schemeWeylCharacterAction_mem_relativeRoots _ hβ.1, ?_⟩
    have := himage.2
    rw [map_nsmul]
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat]
    omega
  -- Clause 5: Coxeter parabolic subgroups are the standard relative Weyl subgroups.
  have hrep (I : Finset (SimpleRoot i ν)) (a : SimpleRoot i ν) (ha : a ∈ I) :
      cs'.simple a ∈ standardRelativeWeylGroup i ν (rootSet i ν I) := by
    rw [hsimple']
    exact (mem_standardRelativeWeylGroup_iff i ν).2
      ⟨_, D.representative_mem_standardLeviPoints hker ν ⟨a, ha, rfl⟩, rfl⟩
  have c5 (I : Finset (SimpleRoot i ν)) :
      standardSubgroup cs' I = standardRelativeWeylGroup i ν (rootSet i ν I) := by
    apply le_antisymm
    · rw [standardSubgroup, Subgroup.closure_le]
      rintro _ ⟨a, ha, rfl⟩
      exact hrep I a ha
    · intro w hw
      obtain ⟨ζ, hζ⟩ := h.exists_standardCocharacter i ν hT hν (rootSet i ν I)
        (by rintro _ ⟨a, -, rfl⟩; exact a.2)
      have hfix (v : relativeWeylGroup i) (hv : v ∈ standardRelativeWeylGroup i ν (rootSet i ν I))
          (χ : characterLattice T) :
          latticePairing T (schemeWeylCharacterAction i v χ) ζ = latticePairing T χ ζ := by
        obtain ⟨m, hm, rfl⟩ := (mem_standardRelativeWeylGroup_iff i ν).1 hv
        exact latticePairing_weylAction_of_mem_dynamicCentralizer i m
          (standardLevi_le_dynamicCentralizer i ν hζ _ hm) χ
      suffices key : ∀ (l : ℕ) (v : relativeWeylGroup i), cs'.length v = l →
          (∀ χ, latticePairing T (schemeWeylCharacterAction i v χ) ζ = latticePairing T χ ζ) →
          v ∈ standardSubgroup cs' I from key _ w rfl (hfix w hw)
      intro l
      induction l using Nat.strong_induction_on with
      | _ l ih =>
        intro v hl hv
        by_cases h1 : v = 1
        · rw [h1]
          exact one_mem _
        obtain ⟨s, hs⟩ := cs'.exists_rightDescent_of_ne_one h1
        have hnot : schemeWeylCharacterAction i v s.1 ∉ positiveRelativeRoots i ν :=
          fun hp => lt_asymm hs ((c3 v s).2 hp)
        have hnegpos : -(schemeWeylCharacterAction i v s.1) ∈ positiveRelativeRoots i ν := by
          by_contra hc
          exact hnot (mem_positiveRelativeRoots_of_neg_not_mem h hT hν
            (schemeWeylCharacterAction_mem_relativeRoots _ s.2.1.1) hc)
        have hle := hζ.pairing_nonneg_of_positive i ν hnegpos
        rw [hpairing_neg, hv] at hle
        have hsI : s ∈ I := by
          by_contra hsI
          have := hζ.2.2 s.1 s.2 (fun ⟨b, hb, hbs⟩ => hsI (by rw [← Subtype.ext hbs]; exact hb))
          omega
        have hvs : v * cs'.simple s ∈ standardSubgroup cs' I := by
          apply ih _ (hl ▸ hs) _ rfl
          intro χ
          rw [map_mul, LinearEquiv.mul_apply, hv, hfix _ (hrep I s hsI)]
        have := mul_mem hvs (simple_mem_standardSubgroup cs' hsI)
        rwa [CoxeterSystem.simple_mul_simple_cancel_right] at this
  exact ⟨h.finite_relativeWeylGroup i, (h.finite_simpleRelativeRoots i hT ν).to_subtype,
    _, cs',
    fun a => ⟨((latticePairing T).flip (D.coroot ⟨a.1, a.2.1.1⟩)).toAddMonoidHom,
      D.pair_self _, c1 a⟩,
    c2, c3, c4, c5⟩

end RelativeRootReflectionData

end ReflectionData

end Langlands.GroupScheme
