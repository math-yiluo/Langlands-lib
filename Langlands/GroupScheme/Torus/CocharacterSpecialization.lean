import Langlands.GroupScheme.CentralSurjectionImage.BimultRigidity
import Langlands.GroupScheme.Torus.CocharacterBaseChange
import Mathlib.RingTheory.Jacobson.Ring

/-! # Specializing diagonalizable homomorphisms over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterSpecialization

open CocharacterDatum CentralSurjectionImage

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left]
    {Λ : Type u} [AddCommGroup Λ]

/-- Points of `G`, as values of the chosen corepresented point functor of `G`. -/
def toFunctor (S : CommAlgCat (CommRingCat.of k)) :
    GroupScheme.affinePoints G S →* (AffineCoordinates.functor G).obj S :=
  (Corepresented.affinePointsEquiv _ (AffineCoordinates.corepresentation G) S).toMonoidHom.comp
    (GroupScheme.affinePointsTarget G (AffineCoordinates.groupSchemeIso G).inv S)

theorem toFunctor_injective (S : CommAlgCat (CommRingCat.of k)) :
    Function.Injective (toFunctor (G := G) S) := by
  intro x y h
  have h' := (Corepresented.affinePointsEquiv _ (AffineCoordinates.corepresentation G) S).injective h
  change x ≫ (coordIso G).inv = y ≫ (coordIso G).inv at h'
  rwa [cancel_mono] at h'

theorem toFunctor_naturality {S T : CommAlgCat (CommRingCat.of k)} (g : S ⟶ T)
    (x : GroupScheme.affinePoints G S) :
    toFunctor T (GroupScheme.affinePointMap G g x) =
      (AffineCoordinates.functor G).map g (toFunctor S x) := by
  change Corepresented.affinePointsEquiv (AffineCoordinates.functor G)
      (AffineCoordinates.corepresentation G) T
      (((algSpec (CommRingCat.of k)).map g.op ≫ x) ≫ (coordIso G).inv) = _
  rw [Category.assoc, Corepresented.affinePointsEquiv_naturality]
  rfl

theorem toFunctor_comp_hom {S : CommAlgCat (CommRingCat.of k)}
    (y : (algSpec (CommRingCat.of k)).obj (op S) ⟶ (Corepresented.groupScheme
      (AffineCoordinates.functor G) (AffineCoordinates.corepresentation G)).X) :
    toFunctor S (y ≫ (AffineCoordinates.groupSchemeIso G).hom.hom.hom) =
      Corepresented.affinePointsEquiv _ (AffineCoordinates.corepresentation G) S y := by
  change Corepresented.affinePointsEquiv (AffineCoordinates.functor G)
      (AffineCoordinates.corepresentation G) S
      ((y ≫ (coordIso G).hom) ≫ (coordIso G).inv) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (p : Lie.AffinePoints G (AddMonoidAlgebra k Λ))

/-- Specialization of `p` along the algebra map `X^ell ↦ c(ell)` classified by a character
`c : Λ → Sˣ`. -/
def specialize (S : CommAlgCat (CommRingCat.of k)) (c : Multiplicative Λ →* Sˣ) :
    GroupScheme.affinePoints G S :=
  (algSpec _).map (Diagonalizable.lift (CommRingCat.of k) Λ c).op ≫ p

theorem lift_mapDomain {S : CommAlgCat (CommRingCat.of k)} {Λ' : Type u} [AddCommGroup Λ']
    (c : Multiplicative Λ' →* Sˣ) (g : Λ →+ Λ') :
    (Diagonalizable.lift (CommRingCat.of k) Λ' c).hom.comp
        (AddMonoidAlgebra.mapDomainAlgHom k k g) =
      (Diagonalizable.lift (CommRingCat.of k) Λ (c.comp (AddMonoidHom.toMultiplicative g))).hom := by
  apply AddMonoidAlgebra.algHom_ext
  · intro ell
    simp [Diagonalizable.lift]
  · exact Subsingleton.elim _ _

omit [IsAffine G.X.left] in
theorem specialize_mul (hp : IsMultG p) (S : CommAlgCat (CommRingCat.of k))
    (c c' : Multiplicative Λ →* Sˣ) :
    specialize p S (c * c') = specialize p S c * specialize p S c' := by
  let L := Diagonalizable.lift (CommRingCat.of k) (Λ × Λ)
    (c.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst Λ Λ)) *
      c'.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd Λ Λ)))
  have h := congrArg (Lie.affineMap G L.hom) hp
  rw [map_mul, expMapG, expMapG, expMapG, ← Lie.affineMap_comp, ← Lie.affineMap_comp,
    ← Lie.affineMap_comp, lift_mapDomain, lift_mapDomain, lift_mapDomain] at h
  have h1 : ((c.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst Λ Λ)) *
      c'.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd Λ Λ))).comp
        (AddMonoidHom.toMultiplicative (diagHom Λ))) = c * c' := by
    ext ell; rfl
  have h2 : ((c.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst Λ Λ)) *
      c'.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd Λ Λ))).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inl Λ Λ))) = c := by
    ext ell; simp
  have h3 : ((c.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst Λ Λ)) *
      c'.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd Λ Λ))).comp
        (AddMonoidHom.toMultiplicative (AddMonoidHom.inr Λ Λ))) = c' := by
    ext ell; simp
  rw [h1, h2, h3] at h
  exact h

omit [IsAffine G.X.left] in
theorem specialize_naturality {S T : CommAlgCat (CommRingCat.of k)} (g : S ⟶ T)
    (c : Multiplicative Λ →* Sˣ) :
    specialize p T ((Diagonalizable.commFunctor (CommRingCat.of k) Λ).map g c) =
      GroupScheme.affinePointMap G g (specialize p S c) := by
  rw [GroupScheme.affinePointMap_apply, specialize, specialize, ← Category.assoc, ← Functor.map_comp,
    ← op_comp]
  congr 3
  apply CommAlgCat.hom_ext
  apply AddMonoidAlgebra.algHom_ext
  · intro ell
    simp [Diagonalizable.lift]
  · exact Subsingleton.elim _ _

omit [IsAffine G.X.left] in
theorem specialize_monomialUnits :
    specialize p (Diagonalizable.algebra (CommRingCat.of k) Λ)
      (Diagonalizable.monomialUnits (CommRingCat.of k) Λ) = p := by
  rw [specialize]
  have : Diagonalizable.lift (CommRingCat.of k) Λ (Diagonalizable.monomialUnits (CommRingCat.of k) Λ) =
      𝟙 _ := by
    apply CommAlgCat.hom_ext
    apply AddMonoidAlgebra.algHom_ext
    · intro ell
      simp [Diagonalizable.lift]
    · exact Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The natural homomorphism `Hom(Λ, Sˣ) → G(S)` given by a multiplicative point `p`. -/
def natOfMult (hp : IsMultG p) :
    Diagonalizable.functor (CommRingCat.of k) Λ ⟶ AffineCoordinates.functor G where
  app S := GrpCat.ofHom (MonoidHom.mk' (fun c => toFunctor S (specialize p S c))
    (fun c c' => by rw [specialize_mul p hp, map_mul]))
  naturality S T g := by
    ext c
    change toFunctor T (specialize p T ((Diagonalizable.commFunctor (CommRingCat.of k) Λ).map g c)) =
      (AffineCoordinates.functor G).map g (toFunctor S (specialize p S c))
    rw [specialize_naturality, toFunctor_naturality]

/-- The homomorphism `D(Λ) ⟶ G` given by a multiplicative point `p` over `k[Λ]`. -/
def homOfMult (hp : IsMultG p) : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G :=
  Corepresented.groupSchemeMap (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ)
      (AffineCoordinates.corepresentation G) (natOfMult p hp) ≫
    (AffineCoordinates.groupSchemeIso G).hom

/-- The universal point of `D(Λ)` is sent to `p`. -/
theorem id_comp_homOfMult (hp : IsMultG p) :
    (𝟙 ((algSpec (CommRingCat.of k)).obj (op (Diagonalizable.algebra (CommRingCat.of k) Λ))) ≫
      (homOfMult p hp).hom.hom : Lie.AffinePoints G (AddMonoidAlgebra k Λ)) = p := by
  apply toFunctor_injective (Diagonalizable.algebra (CommRingCat.of k) Λ)
  rw [homOfMult, Grp.comp_hom_hom, ← Category.assoc, toFunctor_comp_hom,
    Corepresented.groupSchemeMap_affinePoints]
  have h1 : 𝟙 ((algSpec (CommRingCat.of k)).obj (op (Diagonalizable.algebra (CommRingCat.of k) Λ))) =
      (algSpec (CommRingCat.of k)).map (𝟙 (Diagonalizable.algebra (CommRingCat.of k) Λ)).op := by
    rw [op_id, CategoryTheory.Functor.map_id]
  rw [h1, Corepresented.affinePointsEquiv_map]
  have h2 : (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ).homEquiv
      (𝟙 (Diagonalizable.algebra (CommRingCat.of k) Λ)) =
        Diagonalizable.monomialUnits (CommRingCat.of k) Λ := by
    apply MonoidHom.ext
    intro m
    apply Units.ext
    rfl
  change toFunctor _ (specialize p _ ((Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ).homEquiv
    (𝟙 (Diagonalizable.algebra (CommRingCat.of k) Λ)))) = _
  rw [h2, specialize_monomialUnits]


omit [IsAffine G.X.left] in
/-- Coefficient extension preserves multiplicativity for an arbitrary affine group. -/
theorem IsMultG.coeff_map {S S' : Type u} [CommRing S] [Algebra k S]
    [CommRing S'] [Algebra k S']
    {p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)} (hp : IsMultG p)
    (f : S →ₐ[k] S') :
    IsMultG (Lie.affineMap G (AddMonoidAlgebra.mapAlgHom Λ f) p) := by
  unfold IsMultG expMapG at hp ⊢
  have h := congrArg (Lie.affineMap G (AddMonoidAlgebra.mapAlgHom (Λ × Λ) f)) hp
  simpa only [map_mul, ← Lie.affineMap_comp, mapAlgHom_comp_mapDomainAlgHom] using h

/-- Coefficient extension reflects multiplicativity when the coefficient map is injective. -/
theorem IsMultG.of_coeff_map {S S' : Type u} [CommRing S] [Algebra k S]
    [CommRing S'] [Algebra k S'] (f : S →ₐ[k] S') (hf : Function.Injective f)
    {p : Lie.AffinePoints G (AddMonoidAlgebra S Λ)}
    (hp : IsMultG (Lie.affineMap G (AddMonoidAlgebra.mapAlgHom Λ f) p)) : IsMultG p := by
  apply affineMap_injective (AddMonoidAlgebra.mapAlgHom (Λ × Λ) f)
    (mapAlgHom_injective f hf)
  unfold IsMultG expMapG at hp
  simp only [expMapG]
  simpa only [map_mul, ← Lie.affineMap_comp, mapAlgHom_comp_mapDomainAlgHom] using hp

/-- A multiplicative point over an extension field is defined over a finitely generated
subalgebra of that field; extending its coefficients recovers the original point. -/
theorem IsMultG.exists_finiteType_coeffMap_eq
    (hfin : Algebra.FiniteType (CommRingCat.of k) (coordAlgebra G))
    {K : Type u} [Field K] [Algebra k K]
    {x : Lie.AffinePoints G (AddMonoidAlgebra K Λ)} (hx : IsMultG x) :
    ∃ B : Subalgebra k K, Algebra.FiniteType k B ∧
      ∃ y : Lie.AffinePoints G (AddMonoidAlgebra B Λ), IsMultG y ∧
        Lie.affineMap G (AddMonoidAlgebra.mapAlgHom Λ B.val) y = x := by
  classical
  obtain ⟨s, hs⟩ := hfin.out
  let T : Finset K := s.biUnion fun c => ((coord x).hom c).coeff.frange
  let B : Subalgebra k K := Algebra.adjoin k (T : Set K)
  refine ⟨B, Algebra.FiniteType.adjoin_of_finite T.finite_toSet, ?_⟩
  have hgen : ∀ c ∈ s, (coord x).hom c ∈ (AddMonoidAlgebra.mapAlgHom Λ B.val).range := by
    intro c hc
    obtain ⟨y, hy⟩ := exists_mapAlgHom_eq B.val Subtype.val_injective ((coord x).hom c)
      fun ell => by
        by_cases h : ((coord x).hom c).coeff ell = 0
        · rw [h]
          exact zero_mem _
        · refine (AlgHom.mem_range _).mpr ⟨⟨_, Algebra.subset_adjoin ?_⟩, rfl⟩
          exact Finset.mem_biUnion.mpr ⟨c, hc, Finsupp.mem_frange.mpr ⟨h, ell, rfl⟩⟩
    exact ⟨y, hy⟩
  have hall : ∀ c, (coord x).hom c ∈ (AddMonoidAlgebra.mapAlgHom Λ B.val).range := by
    intro c
    have hc : c ∈ Algebra.adjoin (CommRingCat.of k) (s : Set (coordAlgebra G)) := by
      rw [hs]
      trivial
    induction hc using Algebra.adjoin_induction with
    | mem c hc => exact hgen c hc
    | algebraMap r =>
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ (r : k)
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  obtain ⟨y, hy⟩ := exists_affineMap_eq _ (mapAlgHom_injective B.val Subtype.val_injective) x hall
  exact ⟨y, IsMultG.of_coeff_map B.val Subtype.val_injective (hy.symm ▸ hx), hy⟩

/-- Every nonzero finite type algebra over an algebraically closed field has a rational
specialization. -/
theorem exists_specialization [IsAlgClosed k] (B : Type u) [CommRing B] [Algebra k B]
    [Nontrivial B] [Algebra.FiniteType k B] : Nonempty (B →ₐ[k] k) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  let := Ideal.Quotient.field m
  have : Algebra.FiniteType k (B ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) (Ideal.Quotient.mkₐ_surjective k m)
  have : FiniteDimensional k (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
  exact ⟨(IsAlgClosed.lift : (B ⧸ m) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m)⟩

/-- When every base-field multiplicative point is trivial, all multiplicative points over
extension fields are trivial. Rigidity over the coefficient domain reflects a rational
specialization back to the original point. -/
theorem IsMultG.eq_one_of_baseField [IsAlgClosed k]
    [LocallyOfFiniteType G.X.hom]
    (hG : ∀ p : Lie.AffinePoints G (AddMonoidAlgebra k Λ), IsMultG p → p = 1)
    {K : Type u} [Field K] [Algebra k K]
    {x : Lie.AffinePoints G (AddMonoidAlgebra K Λ)} (hx : IsMultG x) : x = 1 := by
  obtain ⟨B, hB, y, hy, hyx⟩ :=
    IsMultG.exists_finiteType_coeffMap_eq (finiteType_coordinateAlgebra G) hx
  let := hB
  obtain ⟨ev⟩ := exists_specialization (k := k) B
  have hy1 : y = 1 := CentralSurjectionImage.IsMultG.eq_one_of_isDomain hy ev (hG _ (IsMultG.coeff_map hy ev))
  rw [← hyx, hy1, map_one]

omit [IsAffine G.X.left] in
/-- Postcomposition preserves multiplicativity without a commutativity hypothesis. -/
theorem isMult_postcomp {H : GroupScheme (Spec (CommRingCat.of k))}
    {S : Type u} [CommRing S] [Algebra k S]
    {x : Lie.AffinePoints H (AddMonoidAlgebra S Λ)} (hx : IsMultG x) (f : H ⟶ G) :
    IsMultG (x ≫ f.hom.hom) := by
  unfold IsMultG expMapG at hx ⊢
  have h := congrArg (GroupScheme.affinePointsTarget H f
    (CommAlgCat.of (CommRingCat.of k) (AddMonoidAlgebra S (Λ × Λ)))) hx
  simpa only [map_mul, GroupScheme.affinePointsTarget_apply, Lie.affineMap_apply,
    Category.assoc] using h

omit [IsAffine G.X.left] in
/-- The universal image point of an actual diagonalizable homomorphism is multiplicative. -/
theorem isMult_hom (f : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G) :
    IsMultG (f.hom.hom : Lie.AffinePoints G (AddMonoidAlgebra k Λ)) := by
  have h : IsMultG (G := (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
      (𝟙 ((algSpec (CommRingCat.of k)).obj
      (op (Diagonalizable.algebra (CommRingCat.of k) Λ)))) :=
    CocharacterDatum.isMult_diagonalizable_id (k := k) (Λ := Λ)
  simpa using isMult_postcomp h f

/-- Vanishing of actual diagonalizable homomorphisms kills multiplicative points. -/
theorem eq_one_of_hom_eq_zero
    (hG : ∀ f : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G, f = 0)
    {x : Lie.AffinePoints G (AddMonoidAlgebra k Λ)} (hx : IsMultG x) : x = 1 := by
  have h := id_comp_homOfMult x hx
  rw [hG (homOfMult x hx)] at h
  simpa only [Grp.zero_hom, Mon.zero_hom, Category.id_comp, ← Hom.one_def] using h.symm

section BaseChange

variable (K : Type u) [Field K] [Algebra k K]

local notation "G_K" => Functor.obj (GroupScheme.baseChange (algebraBaseMap k K)) G

omit [IsAffine G.X.left] in
/-- Exponent maps commute with actual scheme pullback. -/
theorem affineBaseChangeEquiv_expMap {Λ' : Type u} [AddCommGroup Λ'] (g : Λ →+ Λ')
    (x : Lie.AffinePoints G_K (AddMonoidAlgebra K Λ)) :
    Lie.affineBaseChangeEquiv k K G (AddMonoidAlgebra K Λ') (expMapG g x) =
      expMapG g (Lie.affineBaseChangeEquiv k K G (AddMonoidAlgebra K Λ) x) := by
  exact Lie.affineBaseChangeEquiv_naturality k K G
    (AddMonoidAlgebra.mapDomainAlgHom K K g) x

omit [IsAffine G.X.left] in
/-- Multiplicativity is preserved and reflected by actual scheme pullback. -/
theorem isMult_affineBaseChangeEquiv_iff
    (x : Lie.AffinePoints G_K (AddMonoidAlgebra K Λ)) :
    IsMultG (Lie.affineBaseChangeEquiv k K G (AddMonoidAlgebra K Λ) x) ↔ IsMultG x := by
  unfold IsMultG
  rw [← affineBaseChangeEquiv_expMap, ← affineBaseChangeEquiv_expMap,
    ← affineBaseChangeEquiv_expMap, ← map_mul]
  exact (Lie.affineBaseChangeEquiv k K G (AddMonoidAlgebra K (Λ × Λ))).injective.eq_iff

/-- Over an algebraically closed base, vanishing of all diagonalizable homomorphisms
survives every field extension, even for noncommutative affine targets. -/
theorem hom_eq_zero_of_baseField [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    (hG : ∀ f : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G, f = 0)
    (f : (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp ⟶ G_K) : f = 0 := by
  have hx := (isMult_affineBaseChangeEquiv_iff K f.hom.hom).mpr (isMult_hom f)
  have hx1 := IsMultG.eq_one_of_baseField
    (fun p hp => eq_one_of_hom_eq_zero hG hp) hx
  have hf1 : (f.hom.hom : Lie.AffinePoints G_K (AddMonoidAlgebra K Λ)) = 1 := by
    apply (Lie.affineBaseChangeEquiv k K G (AddMonoidAlgebra K Λ)).injective
    simpa only [map_one] using hx1
  apply Grp.hom_ext
  simpa only [Grp.zero_hom, Mon.zero_hom, ← Hom.one_def] using hf1

/-- Vanishing of actual cocharacters survives every extension of an algebraically closed
base field for affine locally finite type targets. -/
theorem gm_hom_eq_zero_of_baseField [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    (hG : ∀ f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, f = 0)
    (f : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ G_K) : f = 0 := by
  let e : (Gm (Spec (CommRingCat.of k))).toGrp ≅
      (Diagonalizable.groupScheme (CommRingCat.of k) (PUnit.{u+1} → ℤ)).toGrp :=
    splitTorus.gmIso _ ≪≫
      (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm
  let eK : (Gm (Spec (CommRingCat.of K))).toGrp ≅
      (Diagonalizable.groupScheme (CommRingCat.of K) (PUnit.{u+1} → ℤ)).toGrp :=
    splitTorus.gmIso _ ≪≫
      (Diagonalizable.splitIso (CommRingCat.of K) (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm
  apply (cancel_epi eK.inv).mp
  rw [comp_zero]
  apply hom_eq_zero_of_baseField K
  intro g
  apply (cancel_epi e.hom).mp
  rw [hG (e.hom ≫ g), comp_zero]

end BaseChange

end Langlands.GroupScheme.CocharacterSpecialization

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, absence of homomorphisms from any fixed
split diagonalizable group is preserved by arbitrary field extension. -/
def DiagonalizableHomVanishingBaseChangeStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (Λ : Type u) [AddCommGroup Λ],
    (∀ f : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G, f = 0) →
    ∀ (K : Type u) [Field K] [Algebra k K]
      (f : (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp ⟶
        (GroupScheme.baseChange (algebraBaseMap k K)).obj G), f = 0

/-- Diagonalizable-homomorphism vanishing specializes from the extension to the base. -/
theorem diagonalizableHomVanishingBaseChange :
    DiagonalizableHomVanishingBaseChangeStatement.{u} := by
  intro k _ _ G _ _ Λ _ hG K _ _ f
  exact CocharacterSpecialization.hom_eq_zero_of_baseField K hG f

end Langlands.GroupScheme
