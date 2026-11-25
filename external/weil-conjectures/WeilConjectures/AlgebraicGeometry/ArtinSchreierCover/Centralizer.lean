/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover.Torsor
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Instances.ZMod
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Automorphisms of the Artin–Schreier cover

The automorphisms of the Artin–Schreier cover `Y ⟶ S` commuting with all translations are the
locally constant functions `S → 𝔽_p`, acting by translation on the fibres; on a connected cover
every automorphism is a translation.
Source: blueprint, lemma-artin-schreier-character-sheaf, steps (6)-(8).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Polynomial Opposite

noncomputable section

namespace AlgebraicGeometry

variable {p : ℕ} [Fact p.Prime] {S : Scheme.{u}} {f : Γ(S, ⊤)} {P : Polynomial Γ(S, ⊤)}

namespace ArtinSchreierCover

variable (hP : P = X ^ p - X - C f) (hchar : (p : Γ(S, ⊤)) = 0)

/-- The translation by `a`, as an endomorphism of the cover in the small étale site. -/
def translationEtale (a : ZMod p) :
    (artinSchreierEtaleTorsor hP hchar).toEtale ⟶ (artinSchreierEtaleTorsor hP hchar).toEtale :=
  MorphismProperty.Over.homMk (artinSchreierTranslation hP hchar a)
    (artinSchreierTranslation_hom hP hchar a)

/-- The pullback to the cover of a locally constant function on `S`. -/
def liftLocallyConstant (b : LocallyConstant S (ZMod p)) :
    C((adjoinRootCover S P).left, ULift.{u + 1} (ZMod p)) :=
  ⟨fun y ↦ ULift.up (b ((adjoinRootCover S P).hom y)),
    continuous_uliftUp.comp (b.continuous.comp (adjoinRootCover S P).hom.base.hom.continuous)⟩

/-- The translation by a locally constant function `b` on `S`: by `b(x)` on the fibre over `x`. -/
def locallyConstantHom (b : LocallyConstant S (ZMod p)) :
    (artinSchreierEtaleTorsor hP hchar).toEtale ⟶ (artinSchreierEtaleTorsor hP hchar).toEtale :=
  (artinSchreierEtaleTorsor hP hchar).smulHom (liftLocallyConstant b) (𝟙 _)

variable {hP hchar}

lemma comp_locallyConstantHom (b : LocallyConstant S (ZMod p))
    (ψ : (artinSchreierEtaleTorsor hP hchar).toEtale ⟶
      (artinSchreierEtaleTorsor hP hchar).toEtale) :
    ψ ≫ locallyConstantHom hP hchar b =
      (artinSchreierEtaleTorsor hP hchar).smulHom (liftLocallyConstant b) ψ := by
  rw [locallyConstantHom, Scheme.EtaleTorsor.comp_smulHom, Category.comp_id]
  congr 1
  ext y
  have h := MorphismProperty.Over.w ψ
  exact congr_arg (fun g : _ ⟶ S ↦ b (g y)) h

lemma locallyConstantHom_add (b b' : LocallyConstant S (ZMod p)) :
    locallyConstantHom hP hchar (b + b') =
      locallyConstantHom hP hchar b' ≫ locallyConstantHom hP hchar b := by
  rw [comp_locallyConstantHom, locallyConstantHom, locallyConstantHom,
    ← Scheme.EtaleTorsor.smulHom_add]
  rfl

lemma locallyConstantHom_zero : locallyConstantHom hP hchar (0 : LocallyConstant S (ZMod p)) =
    𝟙 _ := by
  refine Scheme.EtaleTorsor.etaleHom_ext ?_
  have h := (artinSchreierEtaleTorsor hP hchar).smulHom_const (0 : ULift.{u + 1} (ZMod p)) (𝟙 _)
  rw [(artinSchreierEtaleTorsor hP hchar).zero_vadd] at h
  exact h.trans (Category.comp_id _)

lemma translationEtale_comm (a : ZMod p) (m : ULift.{u + 1} (ZMod p)) :
    (artinSchreierEtaleTorsor hP hchar).vadd m ≫ (translationEtale hP hchar a).left =
      (translationEtale hP hchar a).left ≫ (artinSchreierEtaleTorsor hP hchar).vadd m := by
  exact (artinSchreierTranslation_add hP hchar m.down a).symm.trans
    ((congr_arg (artinSchreierTranslation hP hchar) (add_comm m.down a)).trans
      (artinSchreierTranslation_add hP hchar a m.down))

lemma locallyConstantHom_comm (b : LocallyConstant S (ZMod p)) (a : ZMod p) :
    locallyConstantHom hP hchar b ≫ translationEtale hP hchar a =
      translationEtale hP hchar a ≫ locallyConstantHom hP hchar b := by
  rw [comp_locallyConstantHom, locallyConstantHom, Scheme.EtaleTorsor.smulHom_comp _ _ _ _ _
    (translationEtale_comm a), Category.id_comp]

/-- The translation by a locally constant function, as an isomorphism. -/
def locallyConstantIso (b : LocallyConstant S (ZMod p)) :
    (artinSchreierEtaleTorsor hP hchar).toEtale ≅ (artinSchreierEtaleTorsor hP hchar).toEtale where
  hom := locallyConstantHom hP hchar b
  inv := locallyConstantHom hP hchar (-b)
  hom_inv_id := by rw [← locallyConstantHom_add, neg_add_cancel, locallyConstantHom_zero]
  inv_hom_id := by rw [← locallyConstantHom_add, add_neg_cancel, locallyConstantHom_zero]

variable (hP hchar) in
/-- The translation by a locally constant function, as an automorphism of the cover. -/
def locallyConstantAut : Multiplicative (LocallyConstant S (ZMod p)) →* Aut (adjoinRootCover S P)
    where
  toFun b := .of <| (Scheme.Etale.forget S).mapIso
    (locallyConstantIso (hP := hP) (hchar := hchar) b.toAdd)
  map_one' := by
    apply Aut.ext
    rw [Aut.one_asIso]
    ext : 1
    exact congr_arg (Scheme.Etale.forget S).map locallyConstantHom_zero
  map_mul' b b' := by
    apply Aut.ext
    rw [Aut.mul_asIso]
    ext : 1
    exact (congr_arg (Scheme.Etale.forget S).map (locallyConstantHom_add b.toAdd b'.toAdd)).trans
      ((Scheme.Etale.forget S).map_comp _ _)

lemma locallyConstantAut_hom_left (b : LocallyConstant S (ZMod p)) :
    (locallyConstantAut hP hchar (Multiplicative.ofAdd b)).asIso.hom.left =
      (locallyConstantHom hP hchar b).left :=
  rfl

/-- An automorphism of the cover, as an endomorphism in the small étale site. -/
def autEtale (g : Aut (adjoinRootCover S P)) :
    (artinSchreierEtaleTorsor hP hchar).toEtale ⟶ (artinSchreierEtaleTorsor hP hchar).toEtale :=
  MorphismProperty.Over.homMk g.asIso.hom.left (Over.w g.asIso.hom)

/-- Two points of the cover in the same fibre differ by a translation. -/
lemma exists_translation_apply_eq {y y' : (adjoinRootCover S P).left}
    (h : (adjoinRootCover S P).hom y = (adjoinRootCover S P).hom y') :
    ∃ a : ZMod p, artinSchreierTranslation hP hchar a y' = y := by
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback y y' h
  have hD := isIso_artinSchreier_sigmaDesc hP hchar
  set D := Sigma.desc fun m : ULift.{u + 1} (ZMod p) ↦
      pullback.lift (f := (adjoinRootCover S P).hom) (g := (adjoinRootCover S P).hom)
        (artinSchreierTranslation hP hchar m.down) (𝟙 _) (by simp)
  obtain ⟨m, w, hw⟩ := (sigmaOpenCover fun _ : ULift.{u + 1} (ZMod p) ↦
    (adjoinRootCover S P).left).exists_eq (inv D z)
  have hw' : Sigma.ι (fun _ : ULift.{u + 1} (ZMod p) ↦ (adjoinRootCover S P).left) m w =
      inv D z := hw
  have hzD : D (Sigma.ι (fun _ : ULift.{u + 1} (ZMod p) ↦ (adjoinRootCover S P).left) m w) = z := by
    rw [hw', ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have h1 : Sigma.ι (fun _ : ULift.{u + 1} (ZMod p) ↦ (adjoinRootCover S P).left) m ≫ D ≫
      pullback.fst _ _ = artinSchreierTranslation hP hchar m.down := by simp [D]
  have h2 : Sigma.ι (fun _ : ULift.{u + 1} (ZMod p) ↦ (adjoinRootCover S P).left) m ≫ D ≫
      pullback.snd _ _ = 𝟙 _ := by simp [D]
  have key : (Sigma.ι (fun _ : ULift.{u + 1} (ZMod p) ↦ (adjoinRootCover S P).left) m ≫ D ≫
      pullback.snd _ _ ≫ artinSchreierTranslation hP hchar m.down) w =
      (Sigma.ι (fun _ : ULift.{u + 1} (ZMod p) ↦ (adjoinRootCover S P).left) m ≫ D ≫
        pullback.fst _ _) w := by
    rw [reassoc_of% h2, h1]
  refine ⟨m.down, ?_⟩
  rw [← hz, ← hz', ← hzD]
  exact key

variable (hP hchar) in
/-- **Automorphisms commuting with translations.** The translations by locally constant
functions on `S` are exactly the automorphisms of the Artin–Schreier cover commuting with all
translations by constants, and on every open where such a function is constant they are the
corresponding constant translation. -/
theorem artinSchreier_centralizer :
    ∃ E : Multiplicative (LocallyConstant S (ZMod p)) ≃*
        Subgroup.centralizer (Set.range (artinSchreierAction hP hchar)),
      ∀ (b : LocallyConstant S (ZMod p)) (a : ZMod p) (U : S.Opens),
        (∀ x : U, b x = a) →
        ((adjoinRootCover S P).hom ⁻¹ᵁ U).ι ≫ (E (Multiplicative.ofAdd b)).val.asIso.hom.left =
          ((adjoinRootCover S P).hom ⁻¹ᵁ U).ι ≫
            (artinSchreierAction hP hchar (Multiplicative.ofAdd a)).asIso.hom.left := by
  classical
  set t := artinSchreierEtaleTorsor hP hchar
  set π := (adjoinRootCover S P).hom
  have hsurj : Function.Surjective π := (surjective_adjoinRootCover_artinSchreier hP hchar).surj
  -- the translations by locally constant functions lie in the centralizer
  have hmem (b : Multiplicative (LocallyConstant S (ZMod p))) :
      locallyConstantAut hP hchar b ∈
        Subgroup.centralizer (Set.range (artinSchreierAction hP hchar)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    apply Aut.ext
    rw [Aut.mul_asIso, Aut.mul_asIso]
    ext : 1
    refine Over.OverMorphism.ext ?_
    exact congr_arg (fun g ↦ g.left) (locallyConstantHom_comm (hP := hP) (hchar := hchar)
      b.toAdd a.toAdd)
  let F : Multiplicative (LocallyConstant S (ZMod p)) →*
      Subgroup.centralizer (Set.range (artinSchreierAction hP hchar)) :=
    (locallyConstantAut hP hchar).codRestrict _ hmem
  have hinj : Function.Injective F := by
    intro b b' h
    have h' : locallyConstantHom hP hchar b.toAdd = locallyConstantHom hP hchar b'.toAdd :=
      Scheme.EtaleTorsor.etaleHom_ext (congr_arg (fun g : Subgroup.centralizer _ ↦
        g.val.asIso.hom.left) h)
    have h'' := (t.bijective_smulHom (𝟙 _)).1 h'
    refine Multiplicative.toAdd.injective (LocallyConstant.ext fun x ↦ ?_)
    obtain ⟨y, rfl⟩ := hsurj x
    exact congr_arg ULift.down (DFunLike.congr_fun h'' y)
  have hsurjF : Function.Surjective F := by
    rintro ⟨g, hg⟩
    rw [Subgroup.mem_centralizer_iff] at hg
    obtain ⟨c, hc⟩ := (t.bijective_smulHom (𝟙 _)).2 (autEtale g)
    -- `c` is invariant under translations
    have hinv (a : ZMod p) (y : (adjoinRootCover S P).left) :
        c (artinSchreierTranslation hP hchar a y) = c y := by
      have hcomm := hg _ ⟨Multiplicative.ofAdd a, rfl⟩
      have h1 : autEtale g ≫ translationEtale hP hchar a =
          translationEtale hP hchar a ≫ autEtale g := by
        refine Scheme.EtaleTorsor.etaleHom_ext ?_
        have h3 := congr_arg (fun g : Aut (adjoinRootCover S P) ↦ g.asIso.hom.left) hcomm
        simp only [Aut.mul_asIso, Iso.trans_hom, Over.comp_left] at h3
        exact h3
      rw [← hc, Scheme.EtaleTorsor.smulHom_comp _ _ _ _ _ (translationEtale_comm a),
        Scheme.EtaleTorsor.comp_smulHom, Category.id_comp, Category.comp_id] at h1
      have h2 := (t.bijective_smulHom (translationEtale hP hchar a)).1 h1
      exact (DFunLike.congr_fun h2 y).symm
    -- hence `c` is constant on the fibres and descends to `S`
    have hfib {y y' : (adjoinRootCover S P).left} (h : π y = π y') : c y = c y' := by
      obtain ⟨a, rfl⟩ := exists_translation_apply_eq (hP := hP) (hchar := hchar) h
      exact hinv a y'
    let b₀ : S → ZMod p := fun x ↦ (c (hsurj x).choose).down
    have hb₀ (y : (adjoinRootCover S P).left) : b₀ (π y) = (c y).down :=
      congr_arg ULift.down (hfib (hsurj (π y)).choose_spec)
    have hpre (s : Set (ZMod p)) : b₀ ⁻¹' s = π '' ((fun y ↦ (c y).down) ⁻¹' s) := by
      ext x
      obtain ⟨y, rfl⟩ := hsurj x
      refine ⟨fun hx ↦ ⟨y, by simpa [← hb₀] using hx, rfl⟩, ?_⟩
      rintro ⟨y', hy', hyy'⟩
      simp only [Set.mem_preimage] at hy' ⊢
      rwa [← hyy', hb₀]
    have := isFinite_artinSchreier hP
    have hcont : Continuous fun y ↦ (c y).down := continuous_uliftDown.comp c.continuous
    have hb : IsLocallyConstant b₀ := fun s ↦ by
      have hclosed : IsClosed (b₀ ⁻¹' sᶜ) := by
        rw [hpre]
        exact π.isClosedMap _ ((isClosed_discrete _).preimage hcont)
      simpa using hclosed.isOpen_compl
    refine ⟨Multiplicative.ofAdd ⟨b₀, hb⟩, Subtype.ext ?_⟩
    apply Aut.ext
    ext : 1
    refine Over.OverMorphism.ext ?_
    have hlift : liftLocallyConstant ⟨b₀, hb⟩ = c := by
      ext y
      exact hb₀ y
    exact (congr_arg (fun c ↦ (t.smulHom c (𝟙 _)).left) hlift).trans
      (congr_arg (fun g ↦ g.left) hc)
  refine ⟨MulEquiv.ofBijective F ⟨hinj, hsurjF⟩, fun b a U hb ↦ ?_⟩
  have hle : π ⁻¹ᵁ U ≤ (adjoinRootCover S P).left.fiberOpens (liftLocallyConstant b)
      (ULift.up a) := fun y hy ↦ by
    simp only [Scheme.mem_fiberOpens, liftLocallyConstant, ContinuousMap.coe_mk]
    exact congr_arg ULift.up (hb ⟨π y, hy⟩)
  exact (Scheme.EtaleTorsor.ι_smulHom_left_of_le _ _ _ hle).trans
    (congr_arg (_ ≫ ·) (Category.id_comp _))

variable (hP hchar) in
/-- On a connected Artin–Schreier cover every automorphism is a translation, and the
translations are pairwise distinct. -/
theorem bijective_artinSchreierAction [ConnectedSpace (adjoinRootCover S P).left] :
    Function.Bijective (artinSchreierAction hP hchar) := by
  obtain ⟨y₀⟩ : Nonempty (adjoinRootCover S P).left := inferInstance
  refine ⟨fun a b h ↦ ?_, fun g ↦ ?_⟩
  · have h' : 𝟙 _ ≫ (artinSchreierEtaleTorsor hP hchar).vadd (ULift.up a.toAdd) =
        𝟙 _ ≫ (artinSchreierEtaleTorsor hP hchar).vadd (ULift.up b.toAdd) := by
      rw [Category.id_comp, Category.id_comp]
      exact congr_arg (fun g : Aut (adjoinRootCover S P) ↦ g.asIso.hom.left) h
    exact congr_arg ULift.down ((artinSchreierEtaleTorsor hP hchar).eq_of_comp_vadd_eq _ h' y₀)
  · obtain ⟨c, hc⟩ := ((artinSchreierEtaleTorsor hP hchar).bijective_smulHom (𝟙 _)).2
      (autEtale g)
    have hconst : c = ContinuousMap.const _ (c y₀) :=
      ContinuousMap.ext fun y ↦ PreconnectedSpace.constant
        (inferInstanceAs (PreconnectedSpace (adjoinRootCover S P).left)) c.continuous
    refine ⟨Multiplicative.ofAdd (c y₀).down, ?_⟩
    apply Aut.ext
    ext : 1
    refine Over.OverMorphism.ext ?_
    have h := (artinSchreierEtaleTorsor hP hchar).smulHom_const (c y₀) (𝟙 _)
    have hc' : (artinSchreierEtaleTorsor hP hchar).smulHom c (𝟙 _) = autEtale g := hc
    rw [← hconst] at h
    exact (h.trans (Category.id_comp _)).symm.trans (congr_arg (fun g ↦ g.left) hc')

end ArtinSchreierCover

end AlgebraicGeometry
