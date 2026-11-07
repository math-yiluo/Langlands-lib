import Langlands.GroupScheme.Reductive.LocalSplitRootTransport

/-! # Root parametrizations of all roots by Weyl conjugation of the simple ones -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitCell

section Transport

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- Moving a torus point by the inverse of an exponent automorphism `e` changes the
exponent of a character by `e.symm`. -/
theorem charValue_comp_exponentIso_inv (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) (m : I → ℤ)
    (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) :
    VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I m) Z
        (t ≫ (splitTorus.exponentIso _ I e).inv.hom.hom) =
      VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I (e.symm m)) Z t := by
  rw [VectorGroup.charValue, VectorGroup.charValue, Category.assoc,
    show splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (e.symm m) =
      splitTorus.exponentHom _ I I e.symm.toLinearMap ≫ splitTorus.exponentCharacter _ I m from
      (splitTorus.exponentHom_comp_exponentCharacter _ I I e.symm.toLinearMap m).symm]
  rfl

/-- A root parametrization moves along a group isomorphism that carries the torus to the
torus up to an exponent automorphism `e`; the exponent changes by `e.symm`. -/
theorem IsRootParametrization.comp_iso_of_exponentIso
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {m : I → ℤ} {u : Ga R ⟶ G}
    (hu : IsRootParametrization i m u) (Φ : G ≅ H) (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))
    (h : i ≫ Φ.hom = (splitTorus.exponentIso _ I e).hom ≫ i') :
    IsRootParametrization i' (e.symm m) (u ≫ Φ.hom) where
  represents := by
    have hr := hu.represents.comp_iso Φ
    let σ := splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I e
    have h2 : i' = (splitTorus.exponentIso _ I e).inv ≫ i ≫ Φ.hom := by
      rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have h' : i' ≫ Φ.symm.hom = CommGroupScheme.groupHom σ.symm.hom ≫ i := by
      rw [Iso.symm_hom, Iso.symm_hom, h2, Category.assoc, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
      rfl
    have hs := RelativeRoot.subgroup_comap_of_transport σ.symm Φ.symm h'
      (splitTorus.exponentCharacter _ I (e.symm m))
    have hc : characterLattice.congr σ.symm
        (splitTorus.exponentCharacter (Spec (CommRingCat.of R)) I (e.symm m)) =
          splitTorus.exponentCharacter _ I m := by
      rw [characterLattice.congr_apply, Iso.symm_inv]
      change splitTorus.exponentHom _ I I e.toLinearMap ≫ _ = _
      rw [splitTorus.exponentHom_comp_exponentCharacter]
      simp
    rw [hc, Iso.symm_hom] at hs
    rwa [hs] at hr
  isClosedSubgroup := hu.isClosedSubgroup.comp_iso Φ
  equivariant Z t c := by
    have h2 : i' = (splitTorus.exponentIso _ I e).inv ≫ i ≫ Φ.hom := by
      rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    have ht : t ≫ i'.hom.hom = ((t ≫ (splitTorus.exponentIso _ I e).inv.hom.hom) ≫
        i.hom.hom) ≫ Φ.hom.hom.hom := by
      rw [h2]
      simp only [Grp.comp_hom_hom, Category.assoc]
    rw [rootPoint_comp, rootPoint_comp, ht, ← MonObj.mul_comp, ← GrpObj.inv_comp,
      ← MonObj.mul_comp, hu.equivariant, charValue_comp_exponentIso_inv]

/-- Conjugating a root parametrization by a Weyl point for `f` gives a root parametrization
for the exponent `f.symm m`. -/
theorem IsRootParametrization.comp_innerIso {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {m : I → ℤ} {u : Ga R ⟶ G} (hu : IsRootParametrization i m u)
    {n : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (hn : IsWeylPoint i n f) :
    IsRootParametrization i (f.symm m) (u ≫ (G.innerIso n).hom) :=
  hu.comp_iso_of_exponentIso (G.innerIso n) f hn.isNormalizingPoint

end Transport

section Words

variable {I : Type u} {J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ))

/-- Apply the reflections of a word of roots, the last letter first:
`wordReflect P [j₁, …, jₖ] m = s_{j₁} (⋯ (s_{jₖ} m))`. -/
def wordReflect (l : List J) (m : I → ℤ) : I → ℤ :=
  l.foldr (fun j x => P.reflection j x) m

theorem wordReflect_neg (l : List J) (m : I → ℤ) :
    wordReflect P l (-m) = -wordReflect P l m := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change P.reflection j (wordReflect P l (-m)) = -P.reflection j (wordReflect P l m)
    rw [ih, map_neg]

/-- A simple root together with a word in the simple reflections carrying it to `α`. -/
structure SimpleWord (b : P.Base) (α : J) where
  simple : J
  simple_mem : simple ∈ b.support
  word : List J
  word_mem : ∀ j ∈ word, j ∈ b.support
  root_eq : wordReflect P word (P.root simple) = P.root α

/-- Every root of a finite reduced root datum is carried to a simple root by simple
reflections. -/
theorem nonempty_simpleWord [Finite J] [P.IsReduced] (b : P.Base) (α : J) :
    Nonempty (SimpleWord P b α) := by
  refine b.induction_reflect α (p := fun α => Nonempty (SimpleWord P b α)) ?_ ?_ ?_
  · rintro β ⟨w⟩
    refine ⟨⟨w.simple, w.simple_mem, w.word ++ [w.simple], ?_, ?_⟩⟩
    · intro j hj
      rcases List.mem_append.mp hj with h | h
      · exact w.word_mem j h
      · rw [List.mem_singleton.mp h]
        exact w.simple_mem
    · rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, ← w.root_eq,
        ← wordReflect_neg, ← RootPairing.reflection_apply_self]
      simp only [wordReflect, List.foldr_append, List.foldr_cons, List.foldr_nil]
  · intro β hβ
    exact ⟨⟨β, hβ, [], by simp, rfl⟩⟩
  · rintro β j ⟨w⟩ hj
    refine ⟨⟨w.simple, w.simple_mem, j :: w.word, ?_, ?_⟩⟩
    · intro j' hj'
      rcases List.mem_cons.mp hj' with h | h
      · rw [h]
        exact hj
      · exact w.word_mem j' h
    · rw [RootPairing.root_reflectionPerm, ← w.root_eq]
      rfl

end Words

section Family

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  (P : RootDatum J (I → ℤ) (I → ℤ)) {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- The Weyl point `u_{-a}(-1) u_a(1) u_{-a}(-1)` of the root `a`; the index of `-a` is
`P.reflectionPerm a a`. -/
def rootWeylPoint (u : J → (Ga R ⟶ G)) (a : J) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X :=
  weylPoint (u a) (u (P.reflectionPerm a a))

/-- Conjugation along a word: `wordConj P u [j₁, …, jₖ] w = Ad(N_{j₁}) ∘ ⋯ ∘ Ad(N_{jₖ}) ∘ w`,
where `N_j = rootWeylPoint P u j`. -/
def wordConj (u : J → (Ga R ⟶ G)) : List J → (Ga R ⟶ G) → (Ga R ⟶ G)
  | [], w => w
  | j :: l, w => wordConj u l w ≫ (G.innerIso (rootWeylPoint P u j)).hom

/-- The root parametrization of `α` obtained from the simple root of a chosen word by
conjugation along the word. -/
def weylFamily {b : P.Base} (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G)) (α : J) :
    Ga R ⟶ G :=
  wordConj P u (W α).word (u (W α).simple)

variable {P}

theorem isRootParametrization_wordConj [DecidableEq I]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {u : J → (Ga R ⟶ G)} (l : List J)
    (hw : ∀ j ∈ l, IsWeylPoint i (rootWeylPoint P u j) (P.reflection j))
    {m : I → ℤ} {w : Ga R ⟶ G} (h : IsRootParametrization i m w) :
    IsRootParametrization i (wordReflect P l m) (wordConj P u l w) := by
  induction l with
  | nil => exact h
  | cons j l ih =>
    have h' := (ih fun j' hj' => hw j' (List.mem_cons_of_mem _ hj')).comp_innerIso
      (hw j List.mem_cons_self)
    exact h'

/-- Every member of the Weyl family is a root parametrization of its root. -/
theorem isRootParametrization_weylFamily [DecidableEq I]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {b : P.Base} {u : J → (Ga R ⟶ G)}
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    (W : ∀ α, SimpleWord P b α) (α : J) :
    IsRootParametrization i (P.root α) (weylFamily P W u α) := by
  have h := isRootParametrization_wordConj (W α).word
    (fun j hj => hw j ((W α).word_mem j hj)) (hu _ (W α).simple_mem)
  rw [(W α).root_eq] at h
  exact h

/-- The Weyl point pulled back to a test scheme is the product of the pulled-back root
points. -/
theorem constantPoint_weylPoint (u u' : Ga R ⟶ G) (Z : Over (Spec (CommRingCat.of R))) :
    G.constantPoint (weylPoint u u') Z =
      rootPoint u' Z (-1) * rootPoint u Z 1 * rootPoint u' Z (-1) := by
  rw [← toUnit_comp_eq_constantPoint, weylPoint, MonObj.comp_mul, MonObj.comp_mul,
    comp_rootPoint, comp_rootPoint, map_neg, map_one]

omit [Fintype I] in
theorem map_constantPoint_rootWeylPoint {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    {Z : Over (Spec (CommRingCat.of R))} (Ψ : (Z ⟶ G.X) →* (Z ⟶ H.X)) (a : J)
    (h1 : Ψ (rootPoint (u a) Z 1) = rootPoint (u' a) Z 1)
    (h2 : Ψ (rootPoint (u (P.reflectionPerm a a)) Z (-1)) =
      rootPoint (u' (P.reflectionPerm a a)) Z (-1)) :
    Ψ (G.constantPoint (rootWeylPoint P u a) Z) = H.constantPoint (rootWeylPoint P u' a) Z := by
  rw [rootWeylPoint, rootWeylPoint, constantPoint_weylPoint, constantPoint_weylPoint, map_mul,
    map_mul, h1, h2]

omit [Fintype I] in
theorem map_rootPoint_wordConj {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    {Z : Over (Spec (CommRingCat.of R))} (Ψ : (Z ⟶ G.X) →* (Z ⟶ H.X)) (l : List J)
    (hN : ∀ j ∈ l,
      Ψ (G.constantPoint (rootWeylPoint P u j) Z) = H.constantPoint (rootWeylPoint P u' j) Z)
    {w : Ga R ⟶ G} {w' : Ga R ⟶ H} (hw : ∀ c, Ψ (rootPoint w Z c) = rootPoint w' Z c)
    (c : Γ(Z.left, ⊤)) :
    Ψ (rootPoint (wordConj P u l w) Z c) = rootPoint (wordConj P u' l w') Z c := by
  induction l generalizing c with
  | nil => exact hw c
  | cons j l ih =>
    change Ψ (rootPoint (wordConj P u l w ≫ (G.innerIso (rootWeylPoint P u j)).hom) Z c) =
      rootPoint (wordConj P u' l w' ≫ (H.innerIso (rootWeylPoint P u' j)).hom) Z c
    rw [rootPoint_comp, rootPoint_comp, GroupScheme.comp_innerIso_hom,
      GroupScheme.comp_innerIso_hom, map_mul, map_mul, map_inv,
      ih (fun j' hj' => hN j' (List.mem_cons_of_mem _ hj')), hN j List.mem_cons_self]

omit [Fintype I] in
/-- A homomorphism of point groups that matches the simple-root points and the points
`u_{-a}(-1)` matches the whole Weyl family. -/
theorem map_rootPoint_weylFamily {b : P.Base} (W : ∀ α, SimpleWord P b α)
    {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)} {Z : Over (Spec (CommRingCat.of R))}
    (Ψ : (Z ⟶ G.X) →* (Z ⟶ H.X))
    (hs : ∀ a ∈ b.support, ∀ c, Ψ (rootPoint (u a) Z c) = rootPoint (u' a) Z c)
    (hneg : ∀ a ∈ b.support, Ψ (rootPoint (u (P.reflectionPerm a a)) Z (-1)) =
      rootPoint (u' (P.reflectionPerm a a)) Z (-1))
    (α : J) (c : Γ(Z.left, ⊤)) :
    Ψ (rootPoint (weylFamily P W u α) Z c) = rootPoint (weylFamily P W u' α) Z c :=
  map_rootPoint_wordConj Ψ (W α).word
    (fun j hj => map_constantPoint_rootWeylPoint Ψ j (hs j ((W α).word_mem j hj) 1)
      (hneg j ((W α).word_mem j hj)))
    (hs _ (W α).simple_mem) c

end Family

section Cell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))} {Z : Over (Spec (CommRingCat.of R))}
  (Ψ : (Z ⟶ G.X) →* (Z ⟶ H.X))

omit [Fintype I] in
theorem map_orderedProduct {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    (hu : ∀ α c, Ψ (rootPoint (u α) Z c) = rootPoint (u' α) Z c) {r : ℕ} (e : Fin r → J)
    (c : Fin r → Γ(Z.left, ⊤)) :
    Ψ (orderedProduct u e Z c) = orderedProduct u' e Z c := by
  rw [orderedProduct, orderedProduct, map_list_prod, List.map_ofFn]
  exact congrArg List.prod (congrArg List.ofFn (funext fun k => hu (e k) (c k)))

/-- A homomorphism of point groups that matches the torus and all root parametrizations
matches the big-cell maps. -/
theorem map_comp_cellMap {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {u : J → (Ga R ⟶ G)}
    {u' : J → (Ga R ⟶ H)}
    (hi : ∀ t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
      Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom)
    (hu : ∀ α c, Ψ (rootPoint (u α) Z c) = rootPoint (u' α) Z c)
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J) (x : Z ⟶ cellObj R I m n) :
    Ψ (x ≫ cellMap i u neg pos) = x ≫ cellMap i' u' neg pos := by
  rw [comp_cellMap, comp_cellMap, cellPoint, cellPoint, map_mul, map_mul,
    map_orderedProduct Ψ hu, map_orderedProduct Ψ hu, hi]

/-- Under the same hypotheses, a multiplication relation between cell points in `G` holds
between the corresponding cell points in `H`. -/
theorem cellRelation_of_map {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {u : J → (Ga R ⟶ G)}
    {u' : J → (Ga R ⟶ H)}
    (hi : ∀ t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X,
      Ψ (t ≫ i.hom.hom) = t ≫ i'.hom.hom)
    (hu : ∀ α c, Ψ (rootPoint (u α) Z c) = rootPoint (u' α) Z c)
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J) (x y c : Z ⟶ cellObj R I m n)
    (h : (x ≫ cellMap i u neg pos) * (y ≫ cellMap i u neg pos) = c ≫ cellMap i u neg pos) :
    (x ≫ cellMap i' u' neg pos) * (y ≫ cellMap i' u' neg pos) = c ≫ cellMap i' u' neg pos := by
  have h' := congrArg Ψ h
  rwa [map_mul, map_comp_cellMap Ψ hi hu, map_comp_cellMap Ψ hi hu,
    map_comp_cellMap Ψ hi hu] at h'

end Cell

end Langlands.GroupScheme.LocalSplitCell
