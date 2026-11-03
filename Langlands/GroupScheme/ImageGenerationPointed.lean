import Langlands.GroupScheme.ImageGenerationAppend
import Langlands.GroupScheme.ImageGenerationSubgroup
import Langlands.GroupScheme.ImageGenerationFinitePower
import Langlands.GroupScheme.ImageGenerationGeometry

/-! # Smooth connected generation from a pointed integral morphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ImageGeneration

attribute [local instance] P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.subsingleton_spec_field

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {V : Over (Spec (CommRingCat.of k))}

section Kernels

variable (f : V ⟶ G.X)

/-- The kernel of the global-section map of the `n`-th ordered product. -/
def productKernel (n : ℕ) : Ideal Γ(G.X.left, ⊤) :=
  RingHom.ker (orderedPowerMap f n).left.appTop.hom

/-- Padding by the unit point shows that the product kernels decrease. -/
theorem productKernel_antitone (v₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V)
    (hv₀ : v₀ ≫ f = 1) : Antitone (productKernel f) := by
  intro n m h x hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have hpad := congrArg (fun φ => φ.left.appTop.hom x) (padMap_orderedPowerMap f v₀ hv₀ n d)
  simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply] at hpad
  rw [productKernel, RingHom.mem_ker] at hx ⊢
  rw [← hpad, hx, map_zero]

/-- The product kernels are prime since finite powers of `V` are integral. -/
theorem productKernel_isPrime (hV : FinitePowerGood _ V) (n : ℕ) :
    (productKernel f n).IsPrime := by
  have := (finitePowerGood_finitePower V hV n).isIntegral
  exact RingHom.ker_isPrime _

/-- The product kernels stabilize. -/
theorem exists_productKernel_stable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hV : FinitePowerGood _ V) (v₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ V)
    (hv₀ : v₀ ≫ f = 1) : ∃ N, ∀ m, N ≤ m → productKernel f m = productKernel f N := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsNoetherianRing Γ(G.X.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  exact exists_forall_eq_of_antitone_isPrime _ (productKernel_antitone f v₀ hv₀)
    (productKernel_isPrime f hV)

/-- Equal product kernels give comparable ideal-sheaf kernels. -/
theorem ker_le_ker_of_productKernel_eq [IsAffineHom G.X.hom] {n m : ℕ}
    (h : productKernel f n = productKernel f m) :
    (orderedPowerMap f n).left.ker ≤ (orderedPowerMap f m).left.ker := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
  exact le_of_eq (congrArg _ h)

end Kernels

section Image

variable (f : V ⟶ G.X) (n : ℕ)

/-- The scheme-theoretic image of the `n`-th ordered product, over the base. -/
def productImage : Over (Spec (CommRingCat.of k)) :=
  Over.mk ((orderedPowerMap f n).left.imageι ≫ G.X.hom)

/-- The closed immersion of the product image into the group. -/
def productImageι : productImage f n ⟶ G.X :=
  Over.homMk (orderedPowerMap f n).left.imageι rfl

/-- The factorization of the ordered product through its image. -/
def productToImage : finitePower V n ⟶ productImage f n :=
  Over.homMk (orderedPowerMap f n).left.toImage (by simp [productImage])

@[reassoc]
theorem productToImage_comp : productToImage f n ≫ productImageι f n = orderedPowerMap f n :=
  Over.OverMorphism.ext (orderedPowerMap f n).left.toImage_imageι

instance : IsClosedImmersion (productImageι f n).left :=
  inferInstanceAs (IsClosedImmersion (orderedPowerMap f n).left.imageι)

instance [QuasiCompact (orderedPowerMap f n).left] :
    QuasiCompact (productToImage f n).left :=
  inferInstanceAs (QuasiCompact (orderedPowerMap f n).left.toImage)

instance [QuasiCompact (orderedPowerMap f n).left] :
    IsDominant (productToImage f n).left :=
  inferInstanceAs (IsDominant (orderedPowerMap f n).left.toImage)

theorem ker_productImageι :
    (productImageι f n).left.ker = (orderedPowerMap f n).left.ker :=
  Scheme.IdealSheafData.ker_subschemeι _

theorem isSchemeTheoreticallyDominant_productToImage [IsAffineHom G.X.hom]
    [QuasiCompact (orderedPowerMap f n).left] :
    IsSchemeTheoreticallyDominant (productToImage f n).left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact isSchemeTheoreticallyDominant_toImage (orderedPowerMap f n).left

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {f}

/-- The product image of a good source is good. -/
theorem finitePowerGood_productImage (hV : FinitePowerGood _ V) :
    FinitePowerGood _ (productImage f n) := by
  have hP := finitePowerGood_finitePower V hV n
  have : IsAffine (finitePower V n).left := hP.isAffine
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := isSchemeTheoreticallyDominant_productToImage f n
  have : GeometricallyReduced ((productToImage f n).left ≫ (productImage f n).hom) := by
    rw [Over.w]
    exact hP.2.2.1
  have : GeometricallyIrreducible ((productToImage f n).left ≫ (productImage f n).hom) := by
    rw [Over.w]
    exact hP.2.2.2
  refine ⟨?_, ?_,
    geometricallyReduced_of_isSchemeTheoreticallyDominant (productToImage f n).left _,
    geometricallyIrreducible_of_isSchemeTheoreticallyDominant (productToImage f n).left _⟩
  · change IsAffineHom ((orderedPowerMap f n).left.imageι ≫ G.X.hom)
    infer_instance
  · change LocallyOfFiniteType ((orderedPowerMap f n).left.imageι ≫ G.X.hom)
    infer_instance

omit [LocallyOfFiniteType G.X.hom] in
/-- A stable product image is closed under multiplication. -/
theorem exists_mul_productImage (hV : FinitePowerGood _ V)
    (h : (orderedPowerMap f n).left.ker ≤ (orderedPowerMap f (n + n)).left.ker) :
    ∃ m : productImage f n ⊗ productImage f n ⟶ productImage f n,
      m ≫ productImageι f n =
        (fst _ _ ≫ productImageι f n) * (snd _ _ ≫ productImageι f n) := by
  have : IsAffine (finitePower V n).left := (finitePowerGood_finitePower V hV n).isAffine
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := isSchemeTheoreticallyDominant_productToImage f n
  have := isSchemeTheoreticallyDominant_tensorHom (productToImage f n)
  obtain ⟨t₂, ht₂⟩ := exists_over_factor_of_ker_le (productImageι f n)
    (orderedPowerMap f (n + n)) (by rw [ker_productImageι]; exact h)
  refine exists_over_factor_of_schematic_precomp (productImageι f n)
    (productToImage f n ⊗ₘ productToImage f n) _ (appendPoint (fst _ _) (snd _ _) ≫ t₂) ?_
  rw [MonObj.comp_mul, tensorHom_fst_assoc, tensorHom_snd_assoc, productToImage_comp,
    Category.assoc, ht₂, appendPoint_orderedPowerMap]

end Image

section Assembly

variable [Smooth G.X.hom] [IsAffineHom G.X.hom] {f : V ⟶ G.X}

/-- A closed submonoid receiving `f` with a dominant positive product gives the
smooth connected generated subgroup. -/
theorem exists_generation_of_closedSubmonoid
    {Z : Over (Spec (CommRingCat.of k))} (j : Z ⟶ G.X) [IsClosedImmersion j.left]
    (m : Z ⊗ Z ⟶ Z) (hm : m ≫ j = (fst Z Z ≫ j) * (snd Z Z ≫ j))
    (e : 𝟙_ _ ⟶ Z) (he : e ≫ j = 1)
    [IsAffine (Z ⊗ Z).left] [IsLocallyNoetherian (Z ⊗ Z).left]
    [GeometricallyReduced Z.hom] [GeometricallyIrreducible Z.hom]
    (g : V ⟶ Z) (hg : g ≫ j = f) (n : ℕ) (hn : 0 < n)
    (t : finitePower V n ⟶ Z) (ht : t ≫ j = orderedPowerMap f n) [IsDominant t.left] :
    ∃ D : GeneratedImage f, D.HasSmoothConnectedGeneration := by
  have hpow : orderedPowerMap (G := closedSubgroup j m hm e he) g n = t := by
    have := mono_of_isClosedImmersion_left j
    have h₁ := orderedPowerMap_comp (G := closedSubgroup j m hm e he) g
      (closedSubgroupHom j m hm e he) n
    rw [closedSubgroupHom_hom, hg, ← ht] at h₁
    exact (cancel_mono j).1 h₁
  have hDom : IsDominant (orderedPowerMap (G := closedSubgroup j m hm e he) g n).left := by
    rw [hpow]
    infer_instance
  have : GeometricallyReduced (closedSubgroup j m hm e he).X.hom :=
    ‹GeometricallyReduced Z.hom›
  have : GeometricallyIrreducible (closedSubgroup j m hm e he).X.hom :=
    ‹GeometricallyIrreducible Z.hom›
  exact ⟨_, (GeneratedImage.ofGeometricPower (closedSubgroupHom j m hm e he)
    (isClosedSubgroup_closedSubgroupHom j m hm e he) g
    (by rw [closedSubgroupHom_hom]; exact hg) n hn (hDom := hDom)).2⟩

end Assembly

/-- Over every field, a pointed morphism from an affine geometrically integral scheme of
finite type to a smooth affine group generates a smooth connected closed subgroup. -/
theorem pointedImageGeneration : PointedImageGenerationStatement.{u} := by
  intro k _ G hG hAff V hVAff hVFin hVInt v₀ f hv₀
  have hV := finitePowerGood_of_geometricallyIntegral V hVAff hVFin hVInt
  obtain ⟨N₀, hN₀⟩ := exists_productKernel_stable f hV v₀ hv₀
  have hle : (orderedPowerMap f (1 + N₀)).left.ker ≤
      (orderedPowerMap f (1 + N₀ + (1 + N₀))).left.ker :=
    ker_le_ker_of_productKernel_eq f ((hN₀ _ (by omega)).trans (hN₀ _ (by omega)).symm)
  obtain ⟨m, hm⟩ := exists_mul_productImage (1 + N₀) hV hle
  have hZ := finitePowerGood_productImage (f := f) (1 + N₀) hV
  have hZZ := finitePowerGood_tensor _ _ hZ hZ
  have := hZZ.isAffine
  have := hZZ.isLocallyNoetherian
  have := hZ.2.2.1
  have := hZ.2.2.2
  have : IsAffine (finitePower V (1 + N₀)).left :=
    (finitePowerGood_finitePower V hV _).isAffine
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact exists_generation_of_closedSubmonoid (productImageι f (1 + N₀)) m hm
    (constPoint v₀ (1 + N₀) ≫ productToImage f (1 + N₀))
    (by rw [Category.assoc, productToImage_comp, constPoint_orderedPowerMap f v₀ hv₀])
    (appendPoint (singlePoint V) (toUnit V ≫ constPoint v₀ N₀) ≫ productToImage f (1 + N₀))
    (by
      rw [Category.assoc, productToImage_comp, appendPoint_orderedPowerMap,
        singlePoint_orderedPowerMap, Category.assoc, constPoint_orderedPowerMap f v₀ hv₀,
        MonObj.comp_one, mul_one])
    (1 + N₀) (by omega) (productToImage f (1 + N₀)) (productToImage_comp f _)

end Langlands.GroupScheme.ImageGeneration
