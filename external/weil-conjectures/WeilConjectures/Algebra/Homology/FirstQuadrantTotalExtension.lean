/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.Embedding.Extend

/-! # Extension by zero and first-quadrant totalization

Source: Stacks Project, Section 12.18, Definition 12.18.3 (Tag 012Z),
by the diagonal direct-sum formula for the total complex.
(blueprint: lem-sc-total-extension-nat-arrow-iso)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive ComplexShape

namespace HomologicalComplex₂

namespace firstQuadrantExtension

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Extension in the inner index followed by extension in the outer index. -/
noncomputable abbrev firstQuadrantExtensionFunctor :=
  (embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ) ⋙
    embeddingUpNat.extendFunctor (CochainComplex C ℤ)

variable (K : HomologicalComplex₂ C (up ℕ) (up ℕ))

/-- The extended double complex, with its firstQuadrantExtendedBicomplex type made explicit. -/
noncomputable abbrev firstQuadrantExtendedBicomplex : HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (firstQuadrantExtensionFunctor (C := C)).obj K

variable [HasTotal (firstQuadrantExtendedBicomplex K) (up ℤ)]

/-- The identification of an extended summand in nonnegative bidegree. -/
noncomputable def firstQuadrantExtendedTermIso (a b : ℕ) :
    ((firstQuadrantExtendedBicomplex K).X (a : ℤ)).X (b : ℤ) ≅ (K.X a).X b :=
  (HomologicalComplex.eval C (up ℤ) (b : ℤ)).mapIso
    ((((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ)).obj K).extendXIso
      embeddingUpNat (i := a) rfl) ≪≫
    (K.X a).extendXIso embeddingUpNat (i := b) rfl

/-- The surviving summand included in the integer total degree. -/
private noncomputable def inclusion (a b n : ℕ) (h : a + b = n) :
    (K.X a).X b ⟶ ((firstQuadrantExtendedBicomplex K).total (up ℤ)).X (n : ℤ) :=
  (firstQuadrantExtendedTermIso K a b).inv ≫ (firstQuadrantExtendedBicomplex K).ιTotal (up ℤ)
    (a : ℤ) (b : ℤ) (n : ℤ) (by change (a : ℤ) + (b : ℤ) = (n : ℤ); omega)

/-- The coproduct comparison in a nonnegative total degree. -/
private noncomputable def mapNat (n : ℕ) :
    (K.total (up ℕ)).X n ⟶ ((firstQuadrantExtendedBicomplex K).total (up ℤ)).X (n : ℤ) :=
  K.totalDesc (fun a b h ↦ inclusion K a b n h)

/-- The comparison extended by zero in negative total degrees. -/
private noncomputable def mapX : ∀ n : ℤ,
    ((K.total (up ℕ)).extend embeddingUpNat).X n ⟶
      ((firstQuadrantExtendedBicomplex K).total (up ℤ)).X n
  | .ofNat n => ((K.total (up ℕ)).extendXIso embeddingUpNat (i := n) rfl).hom ≫ mapNat K n
  | .negSucc _ => 0

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [HasTotal (firstQuadrantExtendedBicomplex K) (up ℤ)] in
private lemma termIso_naturality {L : HomologicalComplex₂ C (up ℕ) (up ℕ)}
    (f : K ⟶ L) (a b : ℕ) :
    (((firstQuadrantExtensionFunctor (C := C)).map f).f (a : ℤ)).f (b : ℤ) ≫
      (firstQuadrantExtendedTermIso L a b).hom =
      (firstQuadrantExtendedTermIso K a b).hom ≫ (f.f a).f b := by
  dsimp only [firstQuadrantExtendedTermIso, firstQuadrantExtensionFunctor, Functor.comp_map,
    ComplexShape.Embedding.extendFunctor_map,
    Iso.trans_hom]
  erw [HomologicalComplex.extendMap_f _ embeddingUpNat (i := a) rfl]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  erw [HomologicalComplex.extendMap_f _ embeddingUpNat (i := b) rfl]
  let e := HomologicalComplex.extendXIso
    (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ)).obj L)
    embeddingUpNat (i := a) rfl
  have he := congrArg (fun g ↦ g.f (b : ℤ)) e.inv_hom_id
  dsimp only [e, HomologicalComplex.comp_f, HomologicalComplex.id_f] at he
  dsimp only [Functor.mapIso_hom, HomologicalComplex.eval_map]
  simp only [Category.assoc, reassoc_of% he, Iso.inv_hom_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma mapNat_naturality {L : HomologicalComplex₂ C (up ℕ) (up ℕ)}
    [HasTotal (firstQuadrantExtendedBicomplex L) (up ℤ)] (f : K ⟶ L) (n : ℕ) :
    (total.map f (up ℕ)).f n ≫ mapNat L n =
      mapNat K n ≫
        (total.map ((firstQuadrantExtensionFunctor (C := C)).map f) (up ℤ)).f (n : ℤ) := by
  apply total.hom_ext
  intro a b h
  simp only [Category.assoc, ιTotal_map_assoc, mapNat, ι_totalDesc, ι_totalDesc_assoc,
    inclusion, Category.assoc, ιTotal_map]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact (Iso.comp_inv_eq (firstQuadrantExtendedTermIso L a b)).2 (by
    rw [Category.assoc, termIso_naturality K f a b, Iso.inv_hom_id_assoc])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [HasTotal (firstQuadrantExtendedBicomplex K) (up ℤ)] in
private lemma isZero_term (p q : ℤ) (h : p < 0 ∨ q < 0) :
    IsZero (((firstQuadrantExtendedBicomplex K).X p).X q) := by
  rcases h with hp | hq
  · have hz : IsZero ((firstQuadrantExtendedBicomplex K).X p) :=
      (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ)).obj K).isZero_extend_X
        embeddingUpNat p (by intro a; change (a : ℤ) ≠ p; omega)
    exact (HomologicalComplex.eval C (up ℤ) q).map_isZero hz
  · by_cases hp : 0 ≤ p
    · let e := HomologicalComplex.extendXIso
        (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ)).obj K)
        embeddingUpNat (i := p.toNat) (by change (p.toNat : ℤ) = p; omega)
      exact ((K.X p.toNat).isZero_extend_X embeddingUpNat q
        (by intro b; change (b : ℤ) ≠ q; omega)).of_iso
          ((HomologicalComplex.eval C (up ℤ) q).mapIso e)
    · have hz : IsZero ((firstQuadrantExtendedBicomplex K).X p) :=
        HomologicalComplex.isZero_extend_X
          (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ)).obj K)
          embeddingUpNat p
            (by intro a; change (a : ℤ) ≠ p; omega)
      exact (HomologicalComplex.eval C (up ℤ) q).map_isZero hz

private lemma isZero_total_neg (n : ℤ) (hn : n < 0) :
    IsZero (((firstQuadrantExtendedBicomplex K).total (up ℤ)).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply total.hom_ext
  intro p q h
  exact (isZero_term K p q (by change p + q = n at h; omega)).eq_of_src _ _

/-- The inverse coproduct comparison in a nonnegative degree. -/
private noncomputable def inverseNat (n : ℕ) :
    ((firstQuadrantExtendedBicomplex K).total (up ℤ)).X (n : ℤ) ⟶ (K.total (up ℕ)).X n :=
  (firstQuadrantExtendedBicomplex K).totalDesc (fun p q h ↦
    if hp : 0 ≤ p then
      if hq : 0 ≤ q then
        ((firstQuadrantExtendedBicomplex K).XXIsoOfEq C (up ℤ) (up ℤ)
          (show p = (p.toNat : ℤ) by omega) (show q = (q.toNat : ℤ) by omega)).hom ≫
          (firstQuadrantExtendedTermIso K p.toNat q.toNat).hom ≫
          K.ιTotal (up ℕ) p.toNat q.toNat n (by
            change p.toNat + q.toNat = n
            change p + q = (n : ℤ) at h
            omega)
      else 0
    else 0)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma mapNat_inverseNat (n : ℕ) : mapNat K n ≫ inverseNat K n = 𝟙 _ := by
  apply total.hom_ext
  intro a b h
  delta inverseNat
  simp [mapNat, inclusion, Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma inverseNat_mapNat (n : ℕ) : inverseNat K n ≫ mapNat K n = 𝟙 _ := by
  apply total.hom_ext
  intro p q h
  by_cases hp : 0 ≤ p
  · by_cases hq : 0 ≤ q
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ℤ) = p := ⟨p.toNat, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b : ℕ, (b : ℤ) = q := ⟨q.toNat, by omega⟩
      delta inverseNat
      simp [mapNat, inclusion, Category.assoc]
    · exact (isZero_term K p q (Or.inr (by omega))).eq_of_src _ _
  · exact (isZero_term K p q (Or.inl (by omega))).eq_of_src _ _

private lemma mapNat_isIso (n : ℕ) : IsIso (mapNat K n) :=
  ⟨⟨inverseNat K n, mapNat_inverseNat K n, inverseNat_mapNat K n⟩⟩

private lemma mapX_isIso (n : ℤ) : IsIso (mapX K n) := by
  cases n with
  | ofNat n =>
    have := mapNat_isIso K n
    dsimp only [mapX]
    infer_instance
  | negSucc n =>
    have hs := (K.total (up ℕ)).isZero_extend_X embeddingUpNat (Int.negSucc n)
      (by intro a; change (a : ℤ) ≠ Int.negSucc n; omega)
    have ht := isZero_total_neg K (Int.negSucc n) (by omega)
    exact IsZero.isIso hs ht _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma mapX_naturality {L : HomologicalComplex₂ C (up ℕ) (up ℕ)}
    [HasTotal (firstQuadrantExtendedBicomplex L) (up ℤ)] (f : K ⟶ L) (n : ℤ) :
    (HomologicalComplex.extendMap (total.map f (up ℕ)) embeddingUpNat).f n ≫ mapX L n =
      mapX K n ≫ (total.map ((firstQuadrantExtensionFunctor (C := C)).map f) (up ℤ)).f n := by
  cases n with
  | ofNat n =>
    dsimp only [mapX]
    erw [HomologicalComplex.extendMap_f _ embeddingUpNat (i := n) rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, mapNat_naturality]
    rfl
  | negSucc n =>
    dsimp only [mapX]
    simp only [CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]

end

section

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma horizontal (K : HomologicalComplex₂ C (up ℕ) (up ℕ)) (a a' b : ℕ) :
    ((firstQuadrantExtendedBicomplex K).d (a : ℤ) (a' : ℤ)).f (b : ℤ) ≫
      (firstQuadrantExtendedTermIso K a' b).hom =
      (firstQuadrantExtendedTermIso K a b).hom ≫ (K.d a a').f b := by
  dsimp only [firstQuadrantExtendedTermIso, firstQuadrantExtendedBicomplex,
    firstQuadrantExtensionFunctor, Functor.comp_obj,
    ComplexShape.Embedding.extendFunctor_obj, Iso.trans_hom]
  erw [HomologicalComplex.extend_d_eq _ embeddingUpNat (i := a) (j := a') rfl rfl]
  simp only [HomologicalComplex.comp_f, Category.assoc]
  erw [HomologicalComplex.extendMap_f _ embeddingUpNat (i := b) rfl]
  let e := HomologicalComplex.extendXIso
    (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ)).obj K)
    embeddingUpNat (i := a') rfl
  have he := congrArg (fun g ↦ g.f (b : ℤ)) e.inv_hom_id
  dsimp only [e, HomologicalComplex.comp_f, HomologicalComplex.id_f] at he
  dsimp only [Functor.mapIso_hom, HomologicalComplex.eval_map]
  simp only [Category.assoc, reassoc_of% he, Iso.inv_hom_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma vertical (K : HomologicalComplex₂ C (up ℕ) (up ℕ)) (a b b' : ℕ) :
    ((firstQuadrantExtendedBicomplex K).X (a : ℤ)).d (b : ℤ) (b' : ℤ) ≫
      (firstQuadrantExtendedTermIso K a b').hom =
      (firstQuadrantExtendedTermIso K a b).hom ≫ (K.X a).d b b' := by
  let e := HomologicalComplex.extendXIso
    (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ)).obj K)
    embeddingUpNat (i := a) rfl
  have he := e.hom.comm (b : ℤ) (b' : ℤ)
  dsimp only [firstQuadrantExtendedTermIso, Iso.trans_hom, Functor.mapIso_hom,
    HomologicalComplex.eval_map]
  rw [← Category.assoc]
  erw [← he]
  erw [HomologicalComplex.extend_d_eq _ embeddingUpNat (i := b) (j := b') rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison of nonnegative diagonal coproducts commutes with the differential.
Source: Stacks Project, Definition 12.18.3 (Tag 012Z), the displayed differential
of the total complex; direct verification of step 2 of the parent node.

Proof: precompose both sides with each inclusion K^{a,b} into total degree n.
The total differential is the sum of the horizontal term and the vertical term
with coefficient (-1)^a. The component isomorphisms of both extension functors
intertwine the original horizontal and vertical differentials with their extended
ones, by extend_d_eq and extendMap_f. The target coprojections are precisely
inclusion K (a+1) b (n+1) and inclusion K a (b+1) (n+1). The integer and natural
signs agree: (a:Z).negOnePow = (-1:Zˣ)^a. Hence the two terms agree separately.
Coproduct extensionality proves the equation. This also applies in degree zero:
the single summand is (0,0), and both outgoing components have their usual signs.
No vanishing or boundedness hypothesis beyond nonnegative indexing is used. -/
private lemma mapNat_comm
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (up ℕ) (up ℕ))
    [HasTotal (firstQuadrantExtendedBicomplex K) (up ℤ)] (n : ℕ) :
    mapNat K n ≫ ((firstQuadrantExtendedBicomplex K).total (up ℤ)).d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
      (K.total (up ℕ)).d n (n + 1) ≫ mapNat K (n + 1) := by
  apply total.hom_ext
  intro a b h
  have hab : a + b = n := h
  have h₁ : ComplexShape.π (up ℕ) (up ℕ) (up ℕ) (a + 1, b) = n + 1 := by
    change a + 1 + b = n + 1
    omega
  have h₂ : ComplexShape.π (up ℕ) (up ℕ) (up ℕ) (a, b + 1) = n + 1 := by
    change a + (b + 1) = n + 1
    omega
  have h₁' : ComplexShape.π (up ℤ) (up ℤ) (up ℤ)
      (((a + 1 : ℕ) : ℤ), (b : ℤ)) = ((n + 1 : ℕ) : ℤ) := by
    change ((a + 1 : ℕ) : ℤ) + (b : ℤ) = ((n + 1 : ℕ) : ℤ)
    omega
  have h₂' : ComplexShape.π (up ℤ) (up ℤ) (up ℤ)
      ((a : ℤ), ((b + 1 : ℕ) : ℤ)) = ((n + 1 : ℕ) : ℤ) := by
    change (a : ℤ) + ((b + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ)
    omega
  have ha : (up ℤ).Rel (a : ℤ) ((a + 1 : ℕ) : ℤ) := by
    change (a : ℤ) + 1 = ((a + 1 : ℕ) : ℤ)
    omega
  have hb : (up ℤ).Rel (b : ℤ) ((b + 1 : ℕ) : ℤ) := by
    change (b : ℤ) + 1 = ((b + 1 : ℕ) : ℤ)
    omega
  simp only [mapNat, inclusion, ι_totalDesc_assoc, total_d, comp_add, add_comp,
    Category.assoc, ι_D₁_assoc, ι_D₂_assoc, ι_D₁, ι_D₂]
  rw [K.d₁_eq (up ℕ) (i₁ := a) (i₁' := a + 1) rfl b (n + 1) h₁,
    K.d₂_eq (up ℕ) a (i₂ := b) (i₂' := b + 1) rfl (n + 1) h₂,
    (firstQuadrantExtendedBicomplex K).d₁_eq (up ℤ) ha (b : ℤ) ((n + 1 : ℕ) : ℤ) h₁',
    (firstQuadrantExtendedBicomplex K).d₂_eq (up ℤ) (a : ℤ) hb ((n + 1 : ℕ) : ℤ) h₂']
  have hh : (firstQuadrantExtendedTermIso K a b).inv ≫ ((firstQuadrantExtendedBicomplex K).d (a : ℤ)
      ((a + 1 : ℕ) : ℤ)).f (b : ℤ) =
      (K.d a (a + 1)).f b ≫ (firstQuadrantExtendedTermIso K (a + 1) b).inv := by
    apply (cancel_mono (firstQuadrantExtendedTermIso K (a + 1) b).hom).1
    simp only [Category.assoc, horizontal, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
  have hv : (firstQuadrantExtendedTermIso K a b).inv ≫
    ((firstQuadrantExtendedBicomplex K).X (a : ℤ)).d (b : ℤ)
      ((b + 1 : ℕ) : ℤ) = (K.X a).d b (b + 1) ≫ (firstQuadrantExtendedTermIso K a (b + 1)).inv := by
    apply (cancel_mono (firstQuadrantExtendedTermIso K a (b + 1)).hom).1
    simp only [Category.assoc, vertical, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc]
  have hs : ComplexShape.ε₂ (up ℤ) (up ℤ) (up ℤ) ((a : ℤ), (b : ℤ)) =
      ComplexShape.ε₂ (up ℕ) (up ℕ) (up ℕ) (a, b) := by
    change (a : ℤ).negOnePow = (-1 : ℤˣ) ^ a
    simp [Int.negOnePow]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
    ι_totalDesc, hs]
  erw [reassoc_of% hh, reassoc_of% hv]
  rfl

end

end firstQuadrantExtension

/-- Extending both indices by zero commutes naturally with totalization.
Source: Stacks Project, Section 12.18, Definition 12.18.3 (Tag 012Z);
the reindexing verification below is written by J2.
(blueprint: lem-sc-total-extension-nat-arrow-iso)

Proof: write E for extension of the inner index and then the outer index.
For n<0, every integer pair p+q=n has a negative coordinate, so every summand
of Tot(E K) in degree n is zero. Its degree-n object is therefore a zero object,
as is the extension of Tot(K) in that degree; use their unique isomorphism.
For n>=0, the only potentially nonzero summands have p,q>=0. Restricting the
integer diagonal to those pairs identifies it bijectively with the natural
pairs a+b=n.toNat. On each summand use the two extendXIso isomorphisms
(E K)^{a,b} ≅ K^{a,b}. Define a map of coproducts by these isomorphisms and
an inverse by their inverses. The remaining integer summands are zero and
have unique maps. Checking each coprojection proves both inverse identities.
For consecutive nonnegative degrees these maps commute with the horizontal
and vertical differential: extension uses the same component differentials,
and the total sign (-1)^p equals (-1)^a when p is the integer image of a.
For the boundary -1 to 0 the source is zero; for negative degrees all terms
are zero; other differentials vanish by the shape condition. Thus the maps
are an isomorphism of integer-indexed complexes. Each component is built
from extendXIso and coprojections, both natural in K, so for f:K→L they
identify Tot(E f) with the extension of Tot(f). These two complex
isomorphisms and the naturality square give the asserted arrow isomorphism.
This includes n=0, where the sole surviving summand is (0,0). -/
theorem totalMap_extend_nat_arrow_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    {K L : HomologicalComplex₂ C (up ℕ) (up ℕ)} (f : K ⟶ L)
    [HasTotal (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ) ⋙
      embeddingUpNat.extendFunctor (CochainComplex C ℤ)).obj K) (up ℤ)]
    [HasTotal (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ) ⋙
      embeddingUpNat.extendFunctor (CochainComplex C ℤ)).obj L) (up ℤ)] :
    Nonempty (Arrow.mk (total.map
      (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ) ⋙
        embeddingUpNat.extendFunctor (CochainComplex C ℤ)).map f) (up ℤ)) ≅
      Arrow.mk (HomologicalComplex.extendMap (total.map f (up ℕ)) embeddingUpNat)) := by
  let e (M : HomologicalComplex₂ C (up ℕ) (up ℕ))
      [HasTotal (firstQuadrantExtension.firstQuadrantExtendedBicomplex M) (up ℤ)] :
      (M.total (up ℕ)).extend embeddingUpNat ≅
        (firstQuadrantExtension.firstQuadrantExtendedBicomplex M).total (up ℤ) := by
    have (n : ℤ) : IsIso (firstQuadrantExtension.mapX M n) :=
      firstQuadrantExtension.mapX_isIso M n
    refine HomologicalComplex.Hom.isoOfComponents
      (fun n ↦ asIso (firstQuadrantExtension.mapX M n)) ?_
    intro i j hij
    change firstQuadrantExtension.mapX M i ≫ _ = _ ≫ firstQuadrantExtension.mapX M j
    cases i with
    | ofNat n =>
      have hj : j = ((n + 1 : ℕ) : ℤ) := by change (n : ℤ) + 1 = j at hij; omega
      rw [hj]
      dsimp only [firstQuadrantExtension.mapX]
      erw [HomologicalComplex.extend_d_eq _ embeddingUpNat (i := n)
        (j := n + 1) rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      erw [firstQuadrantExtension.mapNat_comm]
    | negSucc n =>
      exact ((M.total (up ℕ)).isZero_extend_X embeddingUpNat (Int.negSucc n)
        (by intro a; change (a : ℤ) ≠ Int.negSucc n; omega)).eq_of_src _ _
  refine ⟨(Arrow.isoMk (e K) (e L) ?_).symm⟩
  ext n
  exact (firstQuadrantExtension.mapX_naturality K f n).symm

end HomologicalComplex₂
