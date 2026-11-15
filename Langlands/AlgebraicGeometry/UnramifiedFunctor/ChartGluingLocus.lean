import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingGerm

/-! # The open locus of factorization through a chart (SGA 3, XI 3.1)

Let `S` be locally noetherian, let `F` satisfy (F1a), (F1b), (F2) and (F3), and let
`ξ ∈ F(U)` be a monomorphism `U → F`, infinitesimally étale at every point, with `U` locally of
finite type over `S`. For every `η ∈ F(T)`, the set `W ξ η` of points of `T` at whose residue
field `η` factors through `ξ` is open, and `η|_{T'}` factors through `ξ` along `a : T' ⟶ T`
exactly when `a` maps `T'` into `W ξ η` (SGA 3, XI 3.1, (iii) ⇔ (i)).

`ChartGluingGerm` proves that `η` factors through `ξ` near a point `t ∈ W ξ η` at which `T` is
locally noetherian. For an arbitrary `T`, an affine open neighbourhood `Spec B` of `t` maps to
an affine open `Spec R` of `S`, with `R` noetherian; by (F2), `η|_{Spec B}` comes from
`F(Spec B')` for a finitely generated `R`-subalgebra `B'` of `B`, and `Spec B'` is noetherian. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.UnramifiedFunctor.BaseChange

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing

/-! ### An algebra as the filtered colimit of its finitely generated subalgebras -/

section Adjoin

variable (R : Type u) [CommRing R] (B : Type u) [CommRing B] [Algebra R B]

/-- The inclusion `R[s] ⊆ R[s']` for finite subsets `s ⊆ s'` of `B`. -/
def adjoinMap {s s' : Finset B} (h : s ≤ s') :
    Algebra.adjoin R (s : Set B) →ₐ[R] Algebra.adjoin R (s' : Set B) :=
  Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h))

/-- The diagram `s ↦ R[s] ⊆ B` of finitely generated subalgebras of `B`, as rings under `R`. -/
def adjoinDiagram : Finset B ⥤ Under (CommRingCat.of R) where
  obj s := Under.mk (CommRingCat.ofHom (algebraMap R (Algebra.adjoin R (s : Set B))))
  map {s s'} f := Under.homMk
    (CommRingCat.ofHom (adjoinMap R B (leOfHom f)).toRingHom :
      CommRingCat.of (Algebra.adjoin R (s : Set B)) ⟶ CommRingCat.of (Algebra.adjoin R (s' : Set B)))
    (CommRingCat.hom_ext (RingHom.ext fun r ↦ (adjoinMap R B (leOfHom f)).commutes r))
  map_id s := by
    refine Under.UnderMorphism.ext (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
    rfl
  map_comp f g := by
    refine Under.UnderMorphism.ext (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
    rfl

/-- `B` as a cocone over its finitely generated subalgebras. -/
def adjoinCocone : Cocone (adjoinDiagram R B) where
  pt := Under.mk (CommRingCat.ofHom (algebraMap R B))
  ι :=
    { app s := Under.homMk
        (CommRingCat.ofHom (Algebra.adjoin R (s : Set B)).val.toRingHom :
          CommRingCat.of (Algebra.adjoin R (s : Set B)) ⟶ CommRingCat.of B)
        (CommRingCat.hom_ext (RingHom.ext fun r ↦ (Algebra.adjoin R (s : Set B)).val.commutes r))
      naturality s s' f := by
        refine Under.UnderMorphism.ext (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
        rfl }

/-- `B` is the filtered colimit of its finitely generated subalgebras. -/
def isColimitAdjoinCocone : IsColimit (adjoinCocone R B) := by
  refine isColimitOfElements _ (fun (x : B) ↦ ?_) (fun s x y hxy ↦ ?_)
  · exact ⟨{x}, ⟨x, Algebra.subset_adjoin (by simp)⟩, rfl⟩
  · obtain rfl : x = y := Subtype.ext hxy
    exact ⟨s, 𝟙 s, rfl⟩

instance (s : Finset B) [IsNoetherianRing R] : IsNoetherianRing (Algebra.adjoin R (s : Set B)) :=
  have : Algebra.FiniteType R (Algebra.adjoin R (s : Set B)) :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset s)
  Algebra.FiniteType.isNoetherianRing R _

end Adjoin

/-! ### The local factorization -/

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {U : Over S} {ξ : F.obj (op U)}

section

variable (hmono : IsMonoElement F ξ) (hZ : ZariskiSheaf F) (hF : FaithfullyFlatSheaf F)
  (h2 : FilteredColimits F) (hA : AdicLimits F) (hét : ∀ y, InfinitesimallyEtaleAt F ξ y)
  [LocallyOfFiniteType U.hom]
include hmono hZ hF h2 hA hét

/-- SGA 3, XI 3.1 for an affine scheme over the spectrum of a noetherian ring: `η` factors
through `ξ` near every point of `W ξ η`. -/
theorem locFac_of_mem_W_affine {R : Type u} [CommRing R] [IsNoetherianRing R]
    (h₀ : Spec (CommRingCat.of R) ⟶ S) (B : Type u) [CommRing B] [Algebra R B]
    (η : F.obj (op (algebraOver h₀ B))) (t : (algebraOver h₀ B).left) (ht : t ∈ W ξ η) :
    LocFac ξ η t := by
  obtain ⟨s, x, hx⟩ := exists_of_isColimit (good_all hZ h2 h₀) (isColimitAdjoinCocone R B) η
  let π := ((specOver h₀).map ((adjoinCocone R B).ι.app s)).unop
  have hη : F.map π.op x = η := hx
  subst hη
  let X := ((specOver h₀).obj ((adjoinDiagram R B).obj s)).unop
  have : IsLocallyNoetherian X.left :=
    (inferInstance : IsLocallyNoetherian (Spec (CommRingCat.of (Algebra.adjoin R (s : Set B)))))
  have hmem := (mem_W_map_iff hmono hF x π t).mp ht
  exact LocFac.pullback π (locFac_of_mem_W hmono hZ hF h2 hA hét (T := X) x (π.left t) hmem)

/-- SGA 3, XI 3.1, (iii) ⇒ (i), locally: over a locally noetherian base, `η` factors through `ξ`
on an open neighbourhood of every point of `W ξ η`. -/
theorem locFac_of_mem_W' [IsLocallyNoetherian S] {T : Over S} (η : F.obj (op T)) (t : T.left)
    (ht : t ∈ W ξ η) : LocFac ξ η t := by
  obtain ⟨_, ⟨S₀, hS₀, rfl⟩, hts, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (T.hom t)) isOpen_univ
  have hS₀ : IsAffineOpen S₀ := hS₀
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, hVS⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (show t ∈ T.hom ⁻¹ᵁ S₀ from hts)
      (T.hom ⁻¹ᵁ S₀).isOpen
  have hV : IsAffineOpen V := hV
  have : IsNoetherianRing Γ(S, S₀) := IsLocallyNoetherian.component_noetherian ⟨S₀, hS₀⟩
  let : Algebra Γ(S, S₀) Γ(T.left, V) := (T.hom.appLE S₀ V hVS).hom.toAlgebra
  have hw : hV.fromSpec ≫ T.hom =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(S, S₀) Γ(T.left, V))) ≫ hS₀.fromSpec :=
    (hS₀.SpecMap_appLE_fromSpec T.hom hV hVS).symm
  let c : algebraOver hS₀.fromSpec Γ(T.left, V) ⟶ T := Over.homMk hV.fromSpec hw
  have : IsOpenImmersion c.left := by
    change IsOpenImmersion hV.fromSpec
    infer_instance
  obtain ⟨t', rfl⟩ : t ∈ Set.range c.left := by
    change t ∈ Set.range hV.fromSpec
    rw [hV.range_fromSpec]
    exact htV
  exact LocFac.of_map c (locFac_of_mem_W_affine hmono hZ hF h2 hA hét hS₀.fromSpec
    Γ(T.left, V) (F.map c.op η) t' ((mem_W_map_iff hmono hF η c t').mpr ht))

/-- SGA 3, XI 3.1: over a locally noetherian base, `η|_{T'}` factors through `ξ` along
`a : T' ⟶ T` exactly when `a` maps `T'` into `W ξ η`. -/
theorem fac_iff_range_subset_W [IsLocallyNoetherian S] {T T' : Over S} (η : F.obj (op T))
    (a : T' ⟶ T) : Fac ξ η a ↔ Set.range a.left ⊆ W ξ η :=
  fac_iff_range_subset hmono hZ hF
    (fun _ η t ht ↦ locFac_of_mem_W' hmono hZ hF h2 hA hét η t ht) η a

/-- SGA 3, XI 3.1: over a locally noetherian base, `W ξ η` is open. -/
theorem isOpen_W' [IsLocallyNoetherian S] {T : Over S} (η : F.obj (op T)) :
    IsOpen (W ξ η) :=
  isOpen_W hmono hF (fun _ η t ht ↦ locFac_of_mem_W' hmono hZ hF h2 hA hét η t ht) η

end

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing
