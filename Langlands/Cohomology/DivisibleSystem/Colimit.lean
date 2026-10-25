import Langlands.Cohomology.DivisibleSystem
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Colimits of `ℓ`-divisible systems

Harris 1999, §2, p.306, obtains the `ℓ`-divisible system `C_m^•` as the direct limit of the
systems `C_m^{•,H}` as `H` shrinks to the identity. This module constructs colimits of
`ℓ`-divisible systems in an abelian category `C` whose colimits of shape `J` exist and are exact
(`HasExactColimitsOfShape J C`; for filtered `J` this is Grothendieck's AB5). A diagram
`D : J ⥤ DivisibleSystem C ℓ` is first regarded as one `ℓ`-divisible system `diagramSystem D` in
the functor category `J ⥤ C`, whose exactness conditions hold objectwise; the colimit
`colimitSystem D` is its image under the exact functor `colim : (J ⥤ C) ⥤ C`. It is the levelwise
colimit, with the maps `i` and `j` induced on colimits. The cocone `colimitSystemCocone D` is a
colimit cocone (`isColimitColimitSystemCocone`), so `DivisibleSystem C ℓ` has colimits of
shape `J`.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

section FunctorCategory

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C] [Abelian C]

/-- A short complex of functors to an abelian category is exact if it is exact after evaluation
at every object. -/
lemma shortComplex_exact_of_evaluation {S : ShortComplex (J ⥤ C)}
    (h : ∀ j, (S.map ((evaluation J C).obj j)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, Functor.isZero_iff]
  intro j
  exact ((S.map ((evaluation J C).obj j)).exact_iff_isZero_homology.1 (h j)).of_iso
    (S.mapHomologyIso ((evaluation J C).obj j)).symm

/-- A short complex of functors to an abelian category is short exact if it is short exact after
evaluation at every object. -/
lemma shortComplex_shortExact_of_evaluation {S : ShortComplex (J ⥤ C)}
    (h : ∀ j, (S.map ((evaluation J C).obj j)).ShortExact) : S.ShortExact :=
  have : Mono S.f := @NatTrans.mono_of_mono_app _ _ _ _ _ _ S.f fun j => (h j).mono_f
  have : Epi S.g := @NatTrans.epi_of_epi_app _ _ _ _ _ _ S.g fun j => (h j).epi_g
  ⟨shortComplex_exact_of_evaluation fun j => (h j).exact⟩

/-- Multiplication by `ℓ ^ m` on a functor is multiplication by `ℓ ^ m` objectwise. -/
lemma powSMul_app (ℓ m : ℕ) (F : J ⥤ C) (j : J) :
    (powSMul ℓ m F).app j = powSMul ℓ m (F.obj j) := by
  simp [powSMul]

end FunctorCategory

namespace DivisibleSystem

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}
  (D : J ⥤ DivisibleSystem C ℓ)

/-- A diagram of `ℓ`-divisible systems as one `ℓ`-divisible system in the functor category: at
level `m` the functor `j ↦ (D j) m`, with the maps `i` and `j` taken objectwise. The exactness
conditions hold objectwise. -/
@[simps]
def diagramSystem : DivisibleSystem (J ⥤ C) ℓ where
  tower := (D ⋙ forget C ℓ).flip
  inclusion h :=
    { app j := (D.obj j).inclusion h
      naturality _ _ f := ((D.map f).comm h).symm }
  powSMul_eq_zero m := by
    ext j
    rw [powSMul_app]
    exact (D.obj j).powSMul_eq_zero m
  inclusion_comp h := by
    ext j
    exact (D.obj j).inclusion_comp h
  shortExact h := shortComplex_shortExact_of_evaluation fun j => (D.obj j).shortExact h
  torsion_exact h := shortComplex_exact_of_evaluation fun j =>
    shortComplex_exact_congr rfl (powSMul_app _ _ _ _).symm ((D.obj j).torsion_exact h)
  flat a b := shortComplex_exact_of_evaluation fun j =>
    shortComplex_exact_congr (powSMul_app _ _ _ _).symm (powSMul_app _ _ _ _).symm
      ((D.obj j).flat a b)

variable [HasColimitsOfShape J C] [HasExactColimitsOfShape J C]

/-- The colimit of a diagram of `ℓ`-divisible systems, for colimits of shape `J` that exist and
are exact: the image of `diagramSystem D` under `colim : (J ⥤ C) ⥤ C`, that is, the levelwise
colimit with the maps `i` and `j` induced on colimits. -/
abbrev colimitSystem : DivisibleSystem C ℓ :=
  (diagramSystem D).map colim

/-- The coprojection from `D j` to the colimit: at each level, the coprojection of the colimit. -/
@[simps]
def colimitSystemι (j : J) : D.obj j ⟶ colimitSystem D where
  tower :=
    { app m := colimit.ι ((diagramSystem D).tower.obj m) j
      naturality _ _ f := (colimit.ι_map ((diagramSystem D).tower.map f) j).symm }
  comm h := (colimit.ι_map ((diagramSystem D).inclusion h) j).symm

/-- The cocone over `D` formed by the coprojections. -/
@[simps]
def colimitSystemCocone : Cocone D where
  pt := colimitSystem D
  ι :=
    { app j := colimitSystemι D j
      naturality _ _ f := hom_ext (NatTrans.ext (funext fun m =>
        (colimit.w ((diagramSystem D).tower.obj m) f).trans (Category.comp_id _).symm)) }

/-- A cocone over `D` gives, at each level `m`, a cocone over the diagram `j ↦ (D j) m`. -/
@[simps]
def levelCocone (c : Cocone D) (m : ℕᵒᵖ) : Cocone ((diagramSystem D).tower.obj m) where
  pt := c.pt.tower.obj m
  ι :=
    { app j := (c.ι.app j).tower.app m
      naturality _ _ f := NatTrans.congr_app (congrArg Hom.tower (c.ι.naturality f)) m }

/-- The morphism from the colimit to the vertex of a cocone: at each level, the morphism from
the colimit induced by `levelCocone`. -/
@[simps]
def colimitSystemDesc (c : Cocone D) : colimitSystem D ⟶ c.pt where
  tower :=
    { app m := colimit.desc ((diagramSystem D).tower.obj m) (levelCocone D c m)
      naturality X Y f := colimit.hom_ext fun j => by
        refine (ι_colimMap_assoc ((diagramSystem D).tower.map f) j _).trans ?_
        refine (congrArg (_ ≫ ·) (colimit.ι_desc (levelCocone D c Y) j)).trans ?_
        refine ((c.ι.app j).tower.naturality f).trans ?_
        exact (congrArg (· ≫ c.pt.tower.map f) (colimit.ι_desc (levelCocone D c X) j).symm).trans
          (Category.assoc _ _ _) }
  comm h := colimit.hom_ext fun j => by
    refine (ι_colimMap_assoc ((diagramSystem D).inclusion h) j _).trans ?_
    refine (congrArg (_ ≫ ·) (colimit.ι_desc (levelCocone D c _) j)).trans ?_
    refine ((c.ι.app j).comm h).trans ?_
    exact (congrArg (· ≫ c.pt.inclusion h) (colimit.ι_desc (levelCocone D c _) j).symm).trans
      (Category.assoc _ _ _)

/-- The cocone of coprojections is a colimit cocone. -/
def isColimitColimitSystemCocone : IsColimit (colimitSystemCocone D) where
  desc c := colimitSystemDesc D c
  fac _ _ := hom_ext (NatTrans.ext (funext fun _ => colimit.ι_desc _ _))
  uniq c _ hf := hom_ext (NatTrans.ext (funext fun m => colimit.hom_ext fun j =>
    (NatTrans.congr_app (congrArg Hom.tower (hf j)) m).trans
      (colimit.ι_desc (levelCocone D c m) j).symm))

/-- `ℓ`-divisible systems have colimits of every shape `J` whose colimits in `C` exist and are
exact. -/
instance : HasColimitsOfShape J (DivisibleSystem C ℓ) :=
  ⟨fun D => ⟨⟨⟨colimitSystemCocone D, isColimitColimitSystemCocone D⟩⟩⟩⟩

end DivisibleSystem

end Langlands.Cohomology
