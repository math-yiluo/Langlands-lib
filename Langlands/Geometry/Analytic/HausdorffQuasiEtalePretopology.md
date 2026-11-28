# Quasi-étale covers on Hausdorff analytic source objects

The full subcategory consists of quasi-étale objects over an analytic space with Hausdorff sources. In a covering family, the images of finitely many source charts have union a neighbourhood of each point of the target. Right cancellation gives quasi-étale maps between these objects. The analytic pullback is Hausdorff and its common structure morphism is quasi-étale by the compact-domain pullback theorem.

Pulling back a covering preserves its neighbourhoods. At a point of the new target, choose a compact neighbourhood. For each chosen covering chart, the compatible pairs in the product of the chart range with that neighbourhood form a compact set by Hausdorffness of the common target. The inverse image of this set in the analytic pullback is compact and has a finite chart cover. Compatible-point lifting makes the projected images of those charts cover the needed part of the neighbourhood.

For composition of covering families, compactness of each selected chart range gives a finite subcover by the second family of chart-image neighbourhoods. Their images under the first family cover the original neighbourhood. Isomorphisms transport finite chart neighbourhoods by their point homeomorphisms. These properties give the pretopology on the Hausdorff source objects.

The pretopology generates the restriction of the compact-probe topology. A sieve on a Hausdorff object covers exactly when its pushforward to the full quasi-étale site passes the compact-probe test. The Hausdorff comparison converts the test to chart-image neighbourhoods. The image of a sieve under inclusion generates its pushforward, and `hasQuasiEtaleChartNeighborhoods_generate_iff` identifies the neighbourhood condition for these two families.

The Hausdorff objects form a dense subsite over any base. Each compact Hausdorff probe already belongs to the subcategory, so its identity witnesses the finite surjection for the sieve of arrows that factor through Hausdorff objects.

The covering condition and the base-change property apply Berkovich, *Vanishing cycles for formal schemes* (1994), §3, Lemma 3.1 and the quasi-étale pretopology, printed p. 544 (PDF p. 6), to Hausdorff sources. Literature ID `berkovich-1994-vanishing-cycles-formal-schemes`, SHA-256 `f4f7bc00cc46a0a5f72a69d7bbb220bce1d3ed9fd465aeda629f37dfc054bed1`.
