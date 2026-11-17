import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Extending natural pairings along locally bijective maps -/

noncomputable section

universe u v w

namespace Langlands.SheafifyPairing

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C]

/-- The presheaf of pairs, with componentwise restriction. -/
def pairs (P Q : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w where
  obj U := P.obj U × Q.obj U
  map i := TypeCat.ofHom fun s => (P.map i s.1, Q.map i s.2)
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro s
    change (P.map (𝟙 U) s.1, Q.map (𝟙 U) s.2) = s
    simp
  map_comp i j := by
    apply ConcreteCategory.hom_ext
    intro s
    change (P.map (i ≫ j) s.1, Q.map (i ≫ j) s.2) =
      (P.map j (P.map i s.1), Q.map j (Q.map i s.2))
    simp

/-- Apply two natural transformations to the two components. -/
def pairsMap {P Q P' Q' : Cᵒᵖ ⥤ Type w} (f : P ⟶ P') (g : Q ⟶ Q') :
    pairs P Q ⟶ pairs P' Q' where
  app U := TypeCat.ofHom fun s => (f.app U s.1, g.app U s.2)
  naturality i j k := by
    apply ConcreteCategory.hom_ext
    intro s
    change (f.app j (P.map k s.1), g.app j (Q.map k s.2)) =
      (P'.map k (f.app i s.1), Q'.map k (g.app i s.2))
    exact Prod.ext (NatTrans.naturality_apply f k s.1)
      (NatTrans.naturality_apply g k s.2)

variable (J : GrothendieckTopology C)
variable {P Q P' Q' : Cᵒᵖ ⥤ Type w} (f : P ⟶ P') (g : Q ⟶ Q')

instance [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallyInjective J g] :
    Presheaf.IsLocallyInjective J (pairsMap f g) where
  equalizerSieve_mem x y h := by
    change (f.app _ x.1, g.app _ x.2) = (f.app _ y.1, g.app _ y.2) at h
    apply J.superset_covering
      (S := Presheaf.equalizerSieve (F := P) x.1 y.1 ⊓
        Presheaf.equalizerSieve (F := Q) x.2 y.2)
    · intro V i hi
      exact Prod.ext hi.1 hi.2
    · exact J.intersection_covering
        (Presheaf.equalizerSieve_mem J f x.1 y.1 (congrArg Prod.fst h))
        (Presheaf.equalizerSieve_mem J g x.2 y.2 (congrArg Prod.snd h))

instance [Presheaf.IsLocallySurjective J f] [Presheaf.IsLocallySurjective J g] :
    Presheaf.IsLocallySurjective J (pairsMap f g) where
  imageSieve_mem s := by
    apply J.superset_covering
      (S := Presheaf.imageSieve f s.1 ⊓ Presheaf.imageSieve g s.2)
    · rintro V i ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      exact ⟨(x, y), Prod.ext hx hy⟩
    · exact J.intersection_covering
        (Presheaf.imageSieve_mem J f s.1) (Presheaf.imageSieve_mem J g s.2)

variable [J.WEqualsLocallyBijective (Type w)]
variable [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallyInjective J g]
variable [Presheaf.IsLocallySurjective J f] [Presheaf.IsLocallySurjective J g]
variable (H : Sheaf J (Type w)) (b : pairs P Q ⟶ H.obj)

/-- Extend a natural pairing uniquely through two locally bijective maps.
This uses the genuine universal property of sheaves, with no chosen extension as input. -/
def extend : pairs P' Q' ⟶ H.obj :=
  ((J.W_of_isLocallyBijective (pairsMap f g)).homEquiv H.obj H.property).symm b

@[simp]
theorem pairsMap_extend : pairsMap f g ≫ extend J f g H b = b :=
  ((J.W_of_isLocallyBijective (pairsMap f g)).homEquiv H.obj H.property).apply_symm_apply b

/-- The extension agrees with the original pairing on all pairs in the image. -/
@[simp]
theorem extend_apply (U : Cᵒᵖ) (x : P.obj U) (y : Q.obj U) :
    (extend J f g H b).app U (f.app U x, g.app U y) = b.app U (x, y) :=
  congrArg (fun k => k.app U (x, y)) (pairsMap_extend J f g H b)

/-- Agreement after the pair map characterizes the extension. -/
theorem extend_unique (c : pairs P' Q' ⟶ H.obj) (hc : pairsMap f g ≫ c = b) :
    c = extend J f g H b :=
  ((J.W_of_isLocallyBijective (pairsMap f g)) H.obj H.property).1
    (hc.trans (pairsMap_extend J f g H b).symm)

end Langlands.SheafifyPairing
